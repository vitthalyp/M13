InfoASC1 := Print;

HashPerm := function (max, perm )
  local hash, base, point;

  if perm = () then
    return 1;
  fi;

  hash := 0;
  base := 1;
  for point in [1..LargestMovedPointPerm(perm)] do
    base := RemInt(base * point, max);
    hash := hash + (point^perm - 1) * base;
  od;
  return RemInt(hash, max)+1;
end;

HashPerm1 := function( max, perm )
  local hash, digit, degree, i;

  if perm = () then
    return 1;
  fi;

  digit := [];
  degree := LargestMovedPointPerm(perm);
  i := degree;
  while i >= 1 do
    digit[i] := i-i^perm;
    if digit[i] > 0 then
      perm := perm * (i^perm, i);
    fi;
    i := i - 1;
  od;
  return hash + 1;
end;

SqueezeList := function ( list )
  local len, rd, wr;
  len:= Length(list);
  wr := 1;
  for rd in [1..len] do
    if IsBound(list[rd]) then
      if rd > wr then
        list[wr] := list[rd];
      fi;
      wr := wr +1;
    fi;
  od;
  while wr <= len do
    if IsBound(list[wr]) then
      Unbind(list[wr]);
    fi;
    wr := wr + 1;
  od;
end;

ListSqueezed := function (list, func )
  list := ShallowCopy(list);
  SqueezeList(list);
  return List(list, func);
end;

if not IsBound(InfoASC1) then
  InfoASC1 := Ignore;
fi;

MakeGeneratorPairs := function ( G )
  local gps, gps1, x, y, i,hom, genlist, grp;
  grp := G.generators;
  genlist := G.abstractGenerators;
  gps := [];
  for i in [1..Length(genlist)] do
    Add(gps, [grp[i],genlist[i]]);
    Add(gps, [grp[i]^-1,genlist[i]^-1]);
  od;

  Sort(gps);
  x := gps[1];
  gps1 := [];
  for y in gps do
    if y[1] <> x[1] then
      Add(gps1,x);
      x := y;
    fi;
  od;
  Add(gps1, x);
  G.generatorPairs := Set(List(gps1,x->[x[2],x[1]]));
  InfoASC1("#I G.generatorPairs := ", G.generatorPairs, "\n");
end;

EnumeratePermGroup := function ( arg )
  local
    G,
    nrElements,
    wordGens,
    border,
    first, maxFirst,
    table,
    maxTable,
    size,
    minSize,
    maxSize,
    lengths,
    nextLength,
    printedLength,
    x,g,
    xg,xg2,
    h;

  minSize := 1000;
  maxSize := 10000;
  maxTable := 10007;
  maxFirst := 100;

  if Length(arg) = 1 and IsPermGroup(arg[1].group) then
    G := arg[1];
    nrElements := "automatic";
  elif Length(arg) = 2 and IsPermGroup(arg[1].group) and IsInt(arg[2]) then
    G := arg[1];
    nrElements := arg[2];
    if nrElements < 1 then
      Error("Must be positive");
    fi;
  else
    Error("usage failure");
  fi;
  MakeGeneratorPairs(G);

  wordGens := ForAny(G.generatorPairs,x-> Length(x[1])>1);
  if wordGens and nrElements = "automatic" then
    nrElements := minSize;
  fi;

  InfoASC1("#I EnumeratePermGroup uses hash table of size ", maxTable, "\n");
  if not wordGens then
    InfoASC1("#I  exactly 1 permutation of length 0\n");
  fi;

  table := [ ];
  if nrElements <> "automatic" then
    maxTable := nrElements;
    while maxTable > 1 and not IsPrimeInt(maxTable) do
      maxTable := maxTable - 1;
    od;
  fi;
  table[ HashPerm(maxTable, ())] := [[Random(G.generatorPairs)[1]^0, ()]];
  size := 1;
  lengths := [];
  nextLength := 1;
  printedLength := 0;

  border := [ [Random(G.generatorPairs)[1]^0, ()]];
  first := 1;

  while IsBound(border[first]) and size < nrElements do
    x := border[first];
    Unbind(border[first]);
  first := first + 1;
  if first > maxFirst or not IsBound(border[first]) then
    SqueezeList(border);
    first := 1;
  fi;

  for g in G.generatorPairs do
    xg2 := x[2] * g[2];
    h := HashPerm(maxTable,xg2);
    if
      not IsBound(table[h]) or
      ForAll(table[h], y->y[2] <> xg2)
    then
      xg := [x[1] * g[1], xg2];
      if not IsBound(table[h]) then
        table[h] := [];
      fi;
      Add(table[h], xg);
      Add(border, xg);
      size := size + 1;
      if Length(xg[1]) > Length(lengths) then
        while Length(xg[1]) > Length(lengths)+1 do
          Add(lengths,0);
        od;
        Add(lengths,1);
        if Length(lengths) = 1 then
          nextLength := Length(G.generatorPairs);
        elif Length(lengths) = 2 then
          nextLength := nextLength * (nextLength - 1);
        elif lengths[Length(lengths)-2] > 0 then
          nextLength := QuoInt(
            lengths[Length(lengths)-1]^2,
            lengths[Length(lengths)-2]
          );
        fi;

        if Length(lengths) > 1 and not wordGens then
          while printedLength < Length(lengths)-2 do
            printedLength := printedLength + 1;
            InfoASC1(
              "#I  exactly ", lengths[printedLength],
              " permutations of length ", printedLength, "\n"
            );
          od;
          printedLength := printedLength + 1;
          InfoASC1(
            "#I  exactly ", lengths[printedLength],
            " permutations of length ", printedLength,
            " (predicting ", nextLength, " for next length)\n"
          );
        fi;
      else

        if Length(xg[1]) > 0 then
          lengths[Length(xg[1])] := lengths[Length(xg[1])] + 1;
        fi;
      fi;

      if nrElements = "automatic" and lengths[Length(lengths)] = 1 and
          size > minSize and size + nextLength > maxSize or
          IsInt(nrElements) and
          size >= nrElements
      then
        G.shortPairs := Concatenation(Set(table));
        Sort(G.shortPairs);
        if nrElements = "automatic" and Number(border) > 0 then
          Unbind(G.shortPairs[Length(G.shortPairs)]);
        fi;
        IsSet(G.shortPairs);
        return;
      fi;
    fi;
    od;
  od;
  G.shortPairs := Concatenation(Set(table));
  Sort(G.shortPairs);
  if
    nrElements = "automatic" and
    Number(border) > 0 and
    lengths[Length(lengths)] = 1 and
    Length(G.shortPairs[Length(G.shortPairs)][1]) = Length(lengths)
    then
      Unbind(G.shortPairs[Length(G.shortPairs)]);
    fi;
    IsSet(G.shortPairs);
end;

SortLazyElements := function ( list )
  local mp;
  if Length(list) = 0 then
    return [ ];
  fi;
  if IsPerm(list[1]) then
    mp := List(list, NrMovedPointsPerm);
  elif IsList(list[1]) and IsPerm(list[1][2]) then
    mp := List(list, x -> NrMovedPointsPerm(x[2]));
  else
    Error("usage: SortLazyElements( <list-of-perm/[word, perm]>)");
  fi;
  SortParallel(mp,list);
end;

MakeLazyPairs := function ( G )
  local
    lazy, lazy1,
    comms, H,
    mG,
    nG,
    m,
    n,
    x, y,
    i,
    wi, ei,
    ni;

  MakeGeneratorPairs(G);
  if not IsBound(G.shortPairs) then
    EnumeratePermGroup(G);
  fi;
  mG := NrMovedPoints(G.group);
  nG := Length(G.shortPairs[Length(G.shortPairs)][1]);

  InfoASC1(
    "#I MakeLazyPairs called using ",
    Length(G.shortPairs), " short pairs\n"
  );
  lazy := [];
  for x in G.shortPairs do
    m := NrMovedPointsPerm(x[2]);
    n := Length(x[1]);
    if
      0 < m and m < mG and
      Subword(x[1],1,1) <> Subword(x[1], n, n)^-1
    then
      Add(lazy, [m, x[2], x[1]]);
    fi;
  od;

  InfoASC1("#I  adding completed words\n");
  comms := Filtered(lazy, x-> Length(x[3]) = 4 and x[3]^-1 < x[3] and ForAll(G.abstractGenerators, g -> ExponentSumWord(x[3],g) = 0));
  H := rec();
  H.group := Group(List(comms, x -> x[2]),());
  H.abstractGenerators := List(comms, x -> x[3]);
  H.generators := GeneratorsOfGroup(H.group);
  if Size(H.generators) = 0 then
    H.shortPairs := [];
  else
    EnumeratePermGroup(H,Length(lazy));
  fi;
  for x in H.shortPairs do
    m := NrMovedPointsPerm(x[2]);
    n := Length(x[1]);
    if
      0 < m and m < mG and
      n > nG and
      Subgroup(x[1],1,1) <> Subgroup(x[1],n,n)^-1
    then
      Add(lazy, [m, x[2], x[1]]);
    fi;
  od;

  InfoASC1("#I  removing duplicates\n");
  Sort(lazy);
  lazy1 := [ ];
  x := lazy[1];
  for y in lazy do
    if y[2] <> x[2] then
      Add(lazy1, x);
      x := y;
    fi;
  od;
  Add(lazy1, x);
  lazy := lazy1;

  InfoASC1("#I  sorting ", Length(lazy), " pairs for laziness\n");
  G.lazyPairs := List(lazy, x-> [x[3], x[2]]);
  SortLazyElements(G.lazyPairs);
end;

HeuristicBase := function ( G, initialBaseSegment )
  local
    base,
    points,
    p;

  points := MovedPoints(G.group);
  base := [ ];
  for p in initialBaseSegment do
    if p in points and not p in base then
      Add(base, p);
    fi;
  od;
  for p in points do
    if not p in base then
      Add(base, p);
    fi;
  od;
  if IsBound(G.shortPairs) > 0 then
    InfoASC1("#I  choosing base", base, "\n");
  fi;
  return base;
end;

RandomPair := function ( G, length )
  local w, e, g;

  MakeGeneratorPairs(G);
  g := Random(G.generatorPairs);
  w := (g[1])^0;
  e := ();
  while Length(w) < length do
    g := Random(G.generatorPairs);
    w := w * g[1];
    e := e * g[2];
  od;
  return [w,e];
end;

ASCOps := rec();
ASCOps.Print := function ( A )
  local level, T, format, avgLength, sum, nr, num, den;

  format := function ( width, x )
    x := String(x);
    while Length(x) < width do
      x := Concatenation(" ",x);
    od;
    return x;
  end;

  T := [ ];
  for level in [1..Length(A.base)] do
    ASCOps.FlushScreier(A.group, level);

    ASCOps.FlushOrbitGraph(A.group, level);
    Add(T, ASCOps.TracsversalOrbitGraph(A.group, level));
  od;

  Print("ASC(\n","# level basepoint cosets  (orbit size) (max. length) (avg. length)\n");
  for level in [1..Length(A.base)] do
    if not IsBound(A.orbits) or Length(A.orbits[level]) > 1 then
      Print("# ",
      format(5, level), " ",
      format(9, A.base[level]), " ");

      if IsBound(A.orbits) then
        Print(format(6, Length(A.orbits[level])), " ");
      else
        Print(format(6, "unknown"), " ");
      fi;
      Print(format(11, Number(T[level])));
      if IsBound(A.orbits) and Number(T[level]) = Length(A.orbits[level]) then
        if A.schreiers[level].isComplete then
          Print("* ");
        else
          Print("+ ");
        fi;
      else
        Print("  ");
      fi;
      sum := Sum(ListSqueezed(T[level],x-> Length(x[1])));
      nr := Number(T[level]);
      Print(
        format(
          13,
          Concatenation(
            String(QuoInt(sum,nr)),
            ".",
            String(QuoInt(10*sum,nr) mod 10)
          )
        ),
        "\n"
      );
    fi;
  od;
  Print("#\n# total:                ");
  if IsBound(A.orbits) then
    Print(format(6, Sum(List(A.orbits, Length))), " ");
  else
    Print(format(6, "unknown"), " ");
  fi;
  avgLength := 0;
  for level in [1..Length(A.base)] do
    avgLength := avgLength + Sum(ListSqueezed(T[level],x-> Length(x[1])) / Number(T[level]));
  od;
  Print(format(11, Sum(List(T, Number))));
  if IsBound(A.orbits) and Sum(List(T, Number)) = Sum(List(A.orbits, Length)) then
    Print("* ");
  else
    Print(" ");
  fi;
  num := NumeratorRat(avgLength);
  den := DenominatorRat(avgLength);
  Print(format(13,Sum(List(T,Tlevel->Maximum(ListSqueezed(Tlevel, x->Length(x[1])))))), " ",
  format(13, Concatenation(String(QuoInt(num, den)),".",String(QuoInt(10*num,den) mod 10))), "\n");
  Print("#  (orbits: + = complete, * = generating set known)\n)\n");
end;

orbits := function ( S )
  local names, returnList;
  names:=Set(RecNames(S));
  returnList:= [];
  while "orbit" in names do
    Add(returnList,S.orbit);
    S := S.stabilizer;
    names:= Set(RecNames(S));
  od;
  return returnList;
end;

basePoints := function ( S )
  local len, returnList;
  returnList := [];
  len := Length(S.generators);
  while len > 0 do
    Add(returnList, BaseStabChain(S));
    S := S.stabilizer;
    len := Length(S.generators);
  od;
  return returnList;
end;

ASCOps.NewOrbitGraph := function( G, level )
  local A, points, basepoint, orbgraph, p;

  A := G.abstractStabChain;
  basepoint := A.base[level];
  points := A.orbits[level];

  orbgraph := rec(level:=level);
  orbgraph.points := Set(points);
  orbgraph.basepoint := basepoint;

  orbgraph.word := [];
  for p in points do;
    orbgraph.word[p] := [];
  od;

  orbgraph.agenda := [];
  orbgraph.agendaFlush := QuoInt(Binomial(Length(orbgraph.points),2),10);

  if orbgraph.agendaFlush = 0 then
    orbgraph.agendaFlush := 1;
  fi;

  orbgraph.isComplete := false;

  return orbgraph;
end;

ASCOps.FlushOrbitGraph := function ( G, level )
  local orbgraph, w, p, q, r, w_p, w_p_q, update, b, len;

  orbgraph := G.abstractStabChain.orbitGraphs[level];
  if Length(orbgraph.agenda) = 0 then
    return;
  fi;
  InfoASC1("#I flushing agenda of orbit graph on level ", orbgraph.level, "\n");

  update := function ( p, q, word )
    w[p][q] := word;
    AddSet(orbgraph.agenda, [p,q]);
  end;

  w := orbgraph.word;
  while IsBound(orbgraph.agenda[1]) do
    p := orbgraph.agenda[Length(orbgraph.agenda)][1];
    q := orbgraph.agenda[Length(orbgraph.agenda)][2];
    w_p_q := w[p][q];
    Unbind(orbgraph.agenda[Length(orbgraph.agenda)]);

    for r in orbgraph.points do
      if q > r then
        if IsBound(w[p][r]) then
          if IsBound(w[q][r]) then
            if w_p_q * w[q][r] < w[p][r] then
              update(p, r, w_p_q * w[q][r]);
            elif LeftQuotient(w_p_q, w[p][r]) < w[q][r] then
              update(q, r, LeftQuotient(w_p_q, w[p][r]));
            fi;
          else
            update(q, r, LeftQuotient(w_p_q, w[p][r]));
          fi;
        elif IsBound(w[q][r]) then
          update(p, r, w_p_q * w[q][r]);
        fi;
      elif p > r and r > q then
        if IsBound(w[p][r]) then
          if IsBound(w[r][q]) then
            if w_p_q / w[r][q] < w[p][r] then
              update(p, r, w_p_q / w[r][q]);
            elif LeftQuotient(w[p][r], w_p_q) < w[r][q] then
              update(r, q, LeftQuotient(w[p][r], w_p_q));
            fi;
          else
            update(r, q, LeftQuotient(w[p][r], w_p_q));
          fi;
        elif IsBound(w[r][q]) then
          update(p, r, w_p_q / w[r][q]);
        fi;

      elif r > p then

        if IsBound(w[r][p]) then
          if IsBound(w[r][q]) then
            if w[r][q] / w_p_q < w[r][p] then
              update(r, p, w[r][q] / w_p_q);
            elif w[r][p] * w_p_q < w[r][q] then
              update(r, q, w[r][p] * w_p_q);
            fi;
          else
            update(r, q, w[r][p] * w_p_q);
          fi;
        elif IsBound(w[r][q]) then
          update(r, p, w[r][q] / w_p_q);
        fi;
      fi;
    od;
  od;

  if not orbgraph.isComplete then
    orbgraph.isComplete := Number(w[Maximum(orbgraph.points)]) + 1 = Length(orbgraph.points);
    if orbgraph.isComplete then
      InfoASC1("#I level ", orbgraph.level, " is complete\n");
    fi;
  fi;

  if orbgraph.isComplete then
    orbgraph.max := 0;
    for w_p in orbgraph.word do
      for w_p_q in w_p do
        if Length(w_p_q) > orbgraph.max then
          orbgraph.max := Length(w_p_q);
        fi;
      od;
    od;

    orbgraph.maxTransversal := 0;
    orbgraph.minTransversal := orbgraph.max;

    b := orbgraph.basepoint;
    for p in orbgraph.points do
      if p <> b then
        if p > b and IsBound(w[p][b]) then
          len := Length(w[p][b]);
          orbgraph.maxTransversal := Maximum(orbgraph.maxTransversal,len);
          orbgraph.minTransversal := Minimum(orbgraph.minTransversal, len);
        elif p < b and IsBound(w[b][p]) then
          len := Length(w[b][p]);
          orbgraph.maxTransversal := Maximum(orbgraph.maxTransversal,len);
          orbgraph.minTransversal := Minimum(orbgraph.minTransversal, len);
        fi;
      fi;
    od;
  fi;
end;

ASCOps.InsertOrbitGraph := function ( G, level, word, perm )
  local
    orbgraph,
    p, q,
    w,
    wordInv,
    update;

  orbgraph := G.abstractStabChain.orbitGraphs[level];
  if perm = () or orbgraph.isComplete and Length(word) > orbgraph.max then
    return;
  fi;

  w := orbgraph.word;
  wordInv := word^-1;

  update := function ( p, q, word )
    w[p][q] := word;
    AddSet(orbgraph.agenda, [p, q]);
  end;

  for p in orbgraph.points do
    q := p^perm;
    if p > q and ( not IsBound(w[p][q]) or word < w[p][q] ) then
      update(p,q,word);
    elif p < q and ( not IsBound(w[q][p]) or wordInv < w[q][p]) then
      update(q, p, wordInv);
    fi;
  od;

  if Length(orbgraph.agenda) >= orbgraph.agendaFlush then
    ASCOps.FlushOrbitGraph(G, level);
  fi;
end;

ASCOps.TransversalOrbitGraph := function ( G, level )
  local orbgraph, T, b, p;

  ASCOps.FlushOrbitGraph(G, level);
  orbgraph := G.abstractStabChain.orbitGraphs[level];

  T := [];
  b := orbgraph.basepoint;
  T[b] := Random(G.abstractGenerators)^0;
  for p in orbgraph.points do
    if p < b and IsBound(orbgraph.word[b][p]) then
      T[p] := orbgraph.word[b][p];
    elif p > b and IsBound(orbgraph.word[p][b]) then
      T[p] := orbgraph.word[p][b]^-1;
    fi;
    if IsBound(T[p]) then
      T[p] := [T[p], MappedWord(T[p], G.abstractGenerators, G.generators)];
    fi;
  od;
  return T;
end;

ASCOps.NewQuotients := function ( G, level )
  local A, points, basepoint, quots, p;

  A := G.abstractStabChain;
  points := A.orbits[level];
  basepoint := A.base[level];

  quots := rec(
    level := level,
    maxWordLength := "infinity",
    maxCandidates := 100,
    points := points,
    basepoint := basepoint,
    new := [],
    used := [],
    quotients := [],
  );

  for p in quots.points do
    quots.new[p] := [];
    quots.used[p] := [];
  od;
  return quots;
end;

ASCOps.InsertQuotients := function ( G, level, word, perm )
  local quots, p, i;

  quots := G.abstractStabChain.quotients[level];
  if Length(word) > quots.maxWordLength then
    return;
  fi;
  p := quots.basepoint^perm;
  if p = quots.basepoint then
    return;
  fi;

  i := PositionProperty(quots.new[p], x -> x[2] = perm);
  if i = fail then
    Add(quots.new[p], [word,perm]);
  else
    if word < quots.new[p][i][1] then
      quots.new[p][i][1] := word;
    fi;
  fi;
  if Length(quots.new[p]) = quots.maxCandidates + 1 then
    Sort(quots.new[p]);
    Unbind(quots.new[p][Length(quots.new[p])]);
  fi;
end;

nrQuotientNews := function ( G )
  local A, quots, sum, level, p;

  A := G.abstractStabChain;
  quots := A.quotients;
  sum := 0;
  for level in [1..Length(A.base)] do
    for p in [1..Length(quots[level].new)] do
      if IsBound(quots[level].new[p]) then
        sum := sum + Length(quots[level].new[p]);
      fi;
    od;
  od;
  return sum;
end;

ASCOps.FlushQuotients := function ( G, level )
  local quots, N, U, p, n, Npn1, Npn2, Upu, q;

  quots := G.abstractStabChain.quotients[level];
  if ForAll(quots.points,p->Length(quots.new[p]) <= 1) then
    return;
  fi;
  InfoASC1("#I computing quotients on level ", quots.level, "\n");

  N := quots.new;
  U := quots.used;
  for p in quots.points do
    if Length(U[p]) = 0 and Length(N[p]) >= 1 then
      n := Length(N[p]);
      Add(U[p],N[p][n]);
      Unbind(N[p][n]);
    fi;
    if Length(U[p]) >= 1 and Length(N[p]) >= 1 then
      n := Length(N[p]);
      repeat
        Npn1 := N[p][n][1];
        Npn2 := N[p][n][2];
        for Upu in U[p] do
          q := [Upu[1]/Npn1,Upu[2]/Npn2];
          if Length(q[1]) <= quots.maxWordLength then
            Add(quots.quotients, q);
          fi;
        od;

        Add(U[p], N[p][n]);
        Unbind(N[p][n]);
        n := n -1;
      until n = 0;
    fi;
    Sort(U[p]);
    while Length(U[p]) > quots.maxCandidates do
      Unbind(U[p][Length(U[p])]);
    od;
  od;
end;

ASCOps.ReduceMaxWordLength := function ( quots, maxWordLength)
  local p;

  quots.maxWordLength := maxWordLength;
  quots.quotients := Filtered(quots.quotients, x -> Length(x[1]) <= maxWordLength);
  for p in quots.quotients do
    quots.new[p] := Filtered(quots.new[p], x -> Length(x[1]) <= maxWordLength - 1);
    quots.used[p] := Filtered(quots.used[p], x -> Length(x[1]) <= maxWordLength -1);
  od;
end;

ASCOps.QuotientPairs := function ( G, level )
  local quots, Q;
  ASCOps.FlushQuotients( G, level );
  quots := G.abstractStabChain.quotients[level];
  Q := quots.quotients;
  quots.quotients := [];
  return Set(Q);
end;

ASCOps.NewSchreier := function ( G, level )
  local schr, A;

  A := G.abstractStabChain;

  schr := rec();

  schr.level := level;
  schr.maxGenerators := 1000;
  schr.group := Stabilizer(G.group, A.base{[1..level-1]}, OnTuples);
  schr.generators := Set([]);
  schr.generatorSpan := Subgroup(schr.group, []);
  schr.isReduced := true;
  schr.isComplete := false;
  schr.isEnabled := true;

  return schr;
end;

ASCOps.FlushSchreier := function ( G, level )
  local schr, S, x;

  schr := G.abstractStabChain.schreiers[level];
  if schr.isReduced then
    return;
  fi;

  InfoASC1("#I filtering generating set of level ", schr.level, "\n");
  S := Set(schr.geenrators);
  schr.generators := Set([]);
  schr.generatorSpan := Subgroup(schr.group, []);
  for x in S do
    if not x[2] in schr.generatorSpan then
      AddSet(schr.geenratorSpan, x);
      schr.generatorSpan := ClosureGroup(schr.generatorSpan, x[2]);
    fi;
  od;
  schr.isComplete := Size(schr.generatorSpan) = Size(schr.group);
  schr.isReduced := true;
end;

ASCOps.SchreierGeneratingSet := function  ( G, level )
  local schr;
  schr := G.abstractStabChain.schreiers[level];
  if not schr.isComplete then
    return false;
  fi;
  ASCOps.FlushSchreier(G,level);
  return schr.generators;
end;

ASCOps.SchreierPairs := function ( G, level )
  local A, schr, S, T, b, Q, Q1, v, u, s, us, vInv, usv, p;

  A := G.absstractStabChain;
  schr := A.schreiers[level];
  S := ASCOps.SchreierGeneratingSet(G, level);
  if S = false then
    return [];
  fi;

  b := A.base[level];
  T := ASCOps.TransversalOrbitGraph(G, level);

  Q := [];
  for u in T do
    for s in S do
      us := [u[1]*s[1], u[2]*s[2]];
      if IsBound(T[b^us[2]]) then
        vInv := T[b^us[2]];
        usv := [us[1]/vInv[1], us[2] / vInv[2]];
        Add(Q, usv);
      fi;
    od;
  od;
  if Length(Q) = 0 then
    return Length(Q);
  fi;

  Q := List(Q,Reversed);
  Sort(Q);
  Q1:= [];
  u := Q[1];
  for v in Q do
    if v[1] <> u[1] then
      Add(Q1,Reversed(u));
      u := v;
    fi;
  od;
  Add(Q1,Reversed(u));
  Sort(Q1);
  return Q1;
end;

ASCOps.Insert1A := function ( G, word, perm )
  local A, level, base, T, Tp, p, k;

  if perm = () then
    return [0,0];
  fi;

  A:= G.abstractStabChain;
  level := 1;
  base := A.base;
  while base[level]^perm = base[level] do
    level := level +1;
  od;
  ASCOps.InsertOrbitGraph(G, level, word, perm);
  #ASCOps.InsertSchreier(G, level, word, perm);
  ASCOps.InsertQuotients(G, level, word, perm);
  return [0,0];
end;

ASCOps.Insert1 := function( G, word, perm )
local A, level, base, T, Tp, p, k;

if perm = () then
  return [0,0];
fi;

A := G.abstractStabChain;
level := 1;
base := A.base;
while base[level]^perm = base[level] do
  ASCOps.InsertOrbitGraph(G,level,word,perm);
  #ASCOps.InsertSchreier(G, level, word, perm);
  level := level +1;
od;
ASCOps.InsertOrbitGraph(G, level ,word, perm);
#ASCOps.InsertSchreier(G, level, word, perm);
ASCOps.InsertQuotients(G, level, word, perm);
return [0,0];
end;

ASCOps.InsertA := function ( arg )
  local pairs, sum;
  if Length(arg) = 3 then
    return ASCOps.Insert1A(arg[1],arg[2],arg[3]);
  elif Length(arg) = 2 and IsWord(arg[2]) then
    return ASCOps.Insert1A(arg[1],arg[2],MappedWord(arg[2],arg[1].abstractGenerators, arg[1].generators));
  elif Length(arg) = 2 and IsWord(arg[2][1]) and IsPerm(arg[2][2]) then
    return ASCOps.Insert1A(arg[1],arg[2][1], arg[2][2]);
  else
    sum := ASCOps.Insert(arg[1], Random(arg[1].abstractGenerators)^0,());
    for pairs in arg[2] do
      sum := sum + ASCOps.InsertA(arg[1], pairs);
    od;
    return sum;
  fi;
end;

ASCOps.Insert := function ( arg )
  local pairs, sum;

  if Length(arg) = 3 then
    return ASCOps.Insert1(arg[1],arg[2],arg[3]);
  elif Length(arg) = 2 and IsWord(arg[2]) then
    return ASCOps.Insert1(arg[1],arg[2],MappedWord(arg[2],arg[1].abstractGenerators, arg[1].generators));
  elif Length(arg) = 2 and IsWord(arg[2][1]) and IsPerm(arg[2][2]) then
    return ASCOps.Insert1(arg[1], arg[2][1], arg[2][2]);
  else
    sum := ASCOps.Insert1(arg[1],Random(arg[1].abstractGenerators)^0, ());
    for pairs in arg[2] do
      sum := sum + ASCOps.Insert(arg[1], pairs);
    od;
    return sum;
  fi;
end;

ASCOps.InsertRecursive := function( G, pairs)
  local A, T, level, level1, b, s, p, word, perm;

  word := pairs[1];
  perm := pairs[2];
  A := G.abstractStabChain;

  T := [];
  for level in [1..Length(A.base)] do
    Add(T, ASCOps.TransversalOrbitGraph(G, level));
  od;

  s := ASCOps.Insert1(G, Random(G.abstractGenerators)^0, ());
  s := s + ASCOps.Insert1(G, word, perm);
  for level in [1..Length(A.base)] do
    b := A.base[level];
    if not IsBound(T[level][b^perm]) then
      T := [];
      for level1 in [1..Length(A.base)] do
        Add(T, ASCOps.TransversalOrbitGraph(G, level1));
      od;
    fi;
    word := word / T[level][b^perm][1];
    perm := perm / T[level][b^perm][2];
    s := s + ASCOps.TransversalOrbitGraph(G, level1);
    if Length(word) > 20 then
      return s;
    fi;
    if perm = () then
      return s;
    fi;
  od;
  return s;
end;

ASCOps.InsertCollisionPairs1 := function ( G, level)
local useful, T, we1, we2;

InfoASC1("#I useful collisions of level ", level, "\c");
useful := 0;

for T in G.abstractStabChain.transversals[level] do
  for we1 in T do
    for we2 in T do
      useful := useful + ASCOps.Insert1(G, we1[1]/we2[1], we1[2]/we2[2]);
    od;
  od;
od;
InfoASC1(useful, "\n");
return useful;
end;

ASCOps.InsertCollisionPairs := function( G,level )
  local x, useful;

  ASCOps.FlushQuotients(G, level);
  useful := ASCOps.Insert1(G, Random(G.abstractGenerators)^0, ());
  for x in G.abstractStabChain.quotients[level].quotients do
    useful := useful + ASCOps.Insert1(G, x[1], x[2]);
  od;
  G.abstractStabChain.quotients[level].quotients := [];
  return useful;
end;

ASCOps.InsertConjugatedPairs := function (G, lazyPairs, conjugatingPairs )
  local we1, we2, s;

  s := ASCOps.Insert1(G, Random(G.abstractGenerators), ());
  for we1 in lazyPairs do
    for we2 in conjugatingPairs do
      s := s + ASCOps.Insert1(G, we1[1]^we2[2], we1[2]^we2[2]);
    od;
  od;
  return s;
end;

ASCOps.ComputeOrbits := function ( G )
  local base, S, level;

  base := G.abstractStabChain.base;
  S := CopyStabChain(StabChain(G.group,base));
  ExtendStabChain(S, base);
  G.abstractStabChain.orbits := [];
  for level in [1..Length(base)] do
    Add(G.abstractStabChain.orbits,Set(S.orbit));
    S := S.stabilizer;
  od;
end;

ASCOps.New := function ( G, maxLengthTransversal, initialBaseSegment )
  local m, sp, base, T, level, reduce, A;

  base := HeuristicBase(G, initialBaseSegment);
  G.abstractStabChain := rec(
    group := G,
    base := base,
    maxLengthTransversal := maxLengthTransversal,
    transversals := [],
    orbitGraphs := [],
    quotients := [],
    schreiers := [],
    operations := ShallowCopy(ASCOps)
  );

  A := G.abstractStabChain;
  ASCOps.ComputeOrbits(G);

  reduce := Filtered([1..Length(A.base)], i-> Length(A.orbits[i]) > 1);
  A.base := A.base{reduce};
  A.orbits := A.orbits{reduce};

  T := A.transversals;
  for level in [1..Length(A.base)] do
    T[level] := [];
    T[level][A.base[level]] := Set([[Random(G.abstractGenerators)^0, ()]]);
  od;

  for level in [1..Length(A.base)] do
    A.orbitGraphs[level] := ASCOps.NewOrbitGraph(G, level);
    A.quotients[level] := ASCOps.NewQuotients(G,level);
    A.schreiers[level] := ASCOps.NewSchreier(G, level);
  od;
end;

ASCOps.StrongGenerators := function ( G )
  local A, S, S1, s, level, T;

  A := G.abstractStabChain;
  S := [];
  for level in [1..Length(A.base)] do
    T := ASCOps.TransversalOrbitGraph(G, level);
    UniteSet(S, List(Filtered(T, x->x[2] <> ()),x-> x[1]));
  od;

  S1 := [];
  for s in S do
    if not s^-1 in S1 then
      AddSet(S1,s);
    fi;
  od;
  return S1;
end;
