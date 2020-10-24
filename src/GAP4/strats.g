Read("asc.g");
Read("findbase.g");

# create a set given a list
setify := function ( list )
  local rd, wr;

  if Length(list) < 2 then
    return;
  fi;
  Sort(list);
  wr:= 1;
  for rd in [2..Length(list)] do
    if list[rd] <> list[wr] then
      wr := wr +1;
      list[wr] := list[rd];
    fi;
  od;
  while wr < Length(list) do
    wr := wr + 1;
    Unbind(list[wr]);
  od;
  return;
end;

#

makepairsbaselist := function (G, baselist)
  local L;
  L := Filtered(baselist, p->p[1] <> "finalpart");
  return List(L, p -> [p[1],MappedWord(p[1], G.abstractGenerators, G.generators)]);
end;

#

extractbase := function ( baselist )
  return Reversed(Concatenation(List(baselist, p->p[2])));
end;

lengthprofile := function( baselist )
  local L;

  L := Filtered(baselist, p->p[1] <> "finalpart");
  return List(L,p-> Length(p[1]));
end;

insertConjugates := function (G, maxLength)
  local Grp, A, base, points, table, len, il, lp, sp, cpWord, cpPerm, level, coset, t, i;

  A := G.abstractStabChain;
  base := G.base;
  Grp := G.group;
  points := [1..LargestMovedPoint(Grp)];

  table := List([1..Length(base)],level -> List(points,point -> []));

  len := Length(G.lazyPairs);
  for il in [1..len] do
    lp := G.lazyPairs[il];
    for sp in G.shortPairs do
      cpWord := lp[1]^sp[1];
      cpPerm := lp[2]^sp[2];

      level := 1;
      while
        level < Length(base) and
        base[level]^cpPerm = base[level]
        do
          level := level + 1;
        od;

      coset := base[level]^cpPerm;
      t := table[level][coset];
      Add(t, cpWord);

      if Length(t) > 10*maxLength then
        setify(t);
        for i in [maxLength+1..Length(t)] do
          Unbind(t[i]);
        od;
      fi;
    od;
  od;

  for level in [1..Length(base)] do
    for coset in points do
      t := table[level][coset];
      setify(t);
      for i in [maxLength+1..Length(t)] do
        Unbind(t[i]);
      od;
    od;
  od;
  G.conjugatedTable := table;
  return;
end;

AbstractStabChainGenerationOneStrategy := function ( G, nrSP, finalpartofbase)
  local
    baselist,
    base,
    A,
    ins,
    rie,
    i;

  Print("\nSTEP 1: Enumeration of the ",nrSP," shortest words\n");
  Print("**********************************************\n\n");
  EnumeratePermGroup(G, nrSP);

  Print("\nSTEP 2: Generation of lazy elements\n");
  Print("**********************************************\n\n");
  MakeLazyPairs(G);

  Print("\nSTEP 3: Calculation of moved point sets with shortest words\n");
  Print("**********************************************\n\n");
  movedPointsSets(G);

  Print("\nSTEP 4: Calculating baselist\n");
  Print("**********************************************\n\n");
  baselist := findbase(G,1,finalpartofbase);
  base := extractbase(baselist);
  Print("#I baselist:\n", baselist, "\n");
  Print("#I base: ", base,"\n");

  Print("\nSTEP 5: Creating initial stable chain\n");
  Print("**********************************************\n\n");
  ASCOps.New(G, 10, base);
  A := G.abstractStabChain;
  Print(A);
  ins := x -> ASCOps.Insert(G,x);
  rie := i -> ASCOps.InsertCollisionPairs(G,i);

  Print("\nSTEP 6: Calculating conjugates for each in stabchain\n");
  Print("**********************************************\n\n");
  insertConjugates(G,10);

  Print("\n STEP 7: Inseting baselist\n");
  Print("**********************************************\n\n");
  ins(makepairsbaselist(G,baselist));

  Print("\nSTEP 8: Inserting conjugated pairs\n");
  Print("**********************************************\n\n");
  ins(Flat(G.conjugatedTable));
  Print(A);

  Print("\nSTEP 9: Collision pairs\n");
  Print("**********************************************\n\n");
  for i in [Length(A.base), (Length(A.base)-1)..1] do
    rie(i);
  od;
  Print(A);

  Print("\nSTEP 10: Inserting short pairs\n");
  Print("**********************************************\n\n");
  ins(G.shortPairs);
  Print(A);

  Print("\nSTEP 11: Collision pairs\n");
  Print("**********************************************\n\n");
  for i in [Length(A.base),(Length(A.base)-1)..1] do
    rie(i);
  od;
  Print("\n***********************************\n");
  Print("RESULT:\n");
  Print("===========\n\n");
  return A;

end;

AbstractStabChainGenerationAllStrategies := function( G, nrSP, finalpartofbase)
  local
    nrofstrats,
    allbaselists,
    maxlen,
    longbaselists,
    lenprofile,
    quality,
    bestbaselist,
    beststrats,
    base,
    A,
    ins,
    rie,
    i;

  Print("\nSTEP 1: Enumeration of the ", nrSP, " shortest words\n");
  Print("**********************************************\n\n");
  EnumeratePermGroup(G, nrSP);

  Print("\nSTEP 2: Generation of lazy elements\n");
  Print("**********************************************\n\n");
  MakeLazyPairs(G);

  Print("\nSTEP 3: Calculation of moved points sets with shortest words\n");
  Print("**********************************************\n\n");
  movedPointsSets(G);
  nrofstrats := Length(G.movedPointsList[Length(G.movedPointsList)][1]);

  Print("\nSTEP 4: Calculating baselists with ", nrofstrats, " strategies\n");
  Print("**********************************************\n\n");
  allbaselists := findbaseall(G,finalpartofbase);
  maxlen := Maximum(List(allbaselists, Length));
  longbaselists := Filtered(allbaselists, l -> Length(l) = maxlen);
  lenprofile := List(longbaselists, lengthprofile);
  quality := List(lenprofile, l -> Sum(List([1..Length(l)], i-> (Length(l) + 1 - i)*l[i])));
  Print("\n#I weighted sum of wordlengths in longest baselists: ", quality,"\n");

  Print("\nSTEP 5: Choosing best baselist\n");
  Print("**********************************************\n\n");
  bestbaselist := longbaselists[Position(quality,Minimum(quality))];
  beststrats := Filtered([1..nrofstrats], i-> allbaselists[i] = bestbaselist);
  Print("#I best startegies are: ",beststrats,"\n");
  base := extractbase(bestbaselist);
  Print("#I best baselist:\n",bestbaselist,"\n");
  Print("#I base: ",base,"\n");

  Print("\nSTEP 6: Creating initial stabchain\n");
  Print("**********************************************\n\n");
  ASCOps.New(G,10,base);
  A := G.abstractStabChain;
  Print(A);
  ins := x -> ASCOps.Insert(G,x);
  rie := i -> ASCOps.InsertCollisionPairs(G, i);

  Print("\nSTEP 7: Calculating conjugates for each place in stabchain");
  Print("**********************************************\n\n");
  insertConjugates(G,10);

  Print("\nSTEP 8: Inserting baselist\n");
  Print("**********************************************\n\n");
  ins(makepairsbaselist(G, bestbaselist));
  Print(A);

  Print("\nSTEP 9: Inserting short pairs\n");
  Print("**********************************************\n\n");
  ins(G.shortPairs);
  Print(A);

  Print("\nSTEP 10: Inserting Collision pairs\n");
  Print("**********************************************\n\n");
  for i in [Length(A.base),Length(A.base)-1..1] do
    rie(i);
  od;
  Print(A);

  Print("\nSTEP 11: Inserting conjugating pairs\n");
  Print("**********************************************\n\n");
  ins(Flat(G.conjugatedTable));
  Print(A);

  Print("\nSTEP 12: Inserting Collision pairs\n");
  Print("**********************************************\n\n");
  for i in [Length(A.base), Length(A.base)-1..1] do
    rie(i);
  od;

  Print("\n***************\n");
  Print("RESULT:\n");
  Print("*******\n");

  return A;
end;
