movedPointsSets := function ( G )
  local
    lp,
    lp1,
    l, s, l1,
    mp,
    mp1, mp2,
    m, m1,
    i, i1, j;

    if not IsBound(G.shortPairs) then
      EnumeratePermGroup(G);
    fi;
    if not IsBound(G.lazyPairs) then
      MakeLazyPairs(G);
    fi;

    lp := List([1..Length(G.generators)],k->[MovedPoints(G.generators[k]),G.abstractGenerators[k]]);

    for l in G.lazyPairs do
      Add(lp, [MovedPoints(l[2]),l[1]]);
    od;

    Sort(lp);

    l1 := lp[1];
    lp1 := [];
    for l in lp do
      if l[1] <> l1[1] then
        Add(lp1,l1);
        l1:= l;
      fi;
    od;
    Add(lp1,l1);
    lp := lp1;

    Print("#I |{ mp(1) | l in G.lazyPairs }| = ", Length(lp), "\n");
    Print("#I |G.shortPairs|                 = ", Length(G.shortPairs), "\n");

    mp:= [];

    for l in lp do
      if Position(lp, l) mod 100 = 0 then
        Print("\n***",Position(lp,l),"***\n");
      fi;
      mp1 := [];
      for s in G.shortPairs do
        Add(mp1, [OnSets(l[1],s[2]),l[2]^s[1]]);
      od;

      Sort(mp1);
      m1 := mp1[1];
      mp2 := [];
      for m in mp1 do
        if m[1] <> m1[1] then
          Add(mp2, m1);
          m1 := m;
        fi;
      od;
      Add(mp2, m1);
      mp1 := mp2;

      mp2 := [];
      i := 1;
      i1:= 1;

      while i <= Length(mp) and i1 <= Length(mp1) do
        if mp[i][1] < mp1[i1][1] then
          Add(mp2, mp[i]);
          i := i + 1;
        elif mp[i][1] > mp1[i1][1] then
          Add(mp2, mp1[i1]);
          i1 := i1 + 1;
        else
          Add(mp2, Minimum([mp[i],mp1[i1]]));
          i := i+1;
          i1 := i1 + 1;
        fi;
      od;

      if i <= Length(mp) then
        for j in [i..Length(mp)] do
          Add(mp2,mp[j]);
        od;
      fi;

      if i1 <= Length(mp1) then
        for j in [i1..Length(mp1)] do
          Add(mp2, mp1[j]);
        od;
      fi;

      mp := mp2;
      Print(Length(mp), "\c");
    od;

    Print("\n");

    Print("#I sorting by length of word\n");
    for m in mp do
      m1 := m[1];
      m[1] := m[2];
      m[2] := m1;
    od;
    Sort(mp);
    G.movedPointsList := mp;
    return;
  end;
findbaseinitial := function( G, maxwordlength, finalpartofbase)
  local
    mp,
    max,
    fin,
    mp1,
    i,
    t,
    len, len1,
    min,
    baselist,
    points,
    allpoints;

  if not IsBound(G.movedPointsList) then
    Error("G.movedPointsList is not present");
  fi;

  mp := ShallowCopy(G.movedPointsList);
  max := maxwordlength;
  fin:= finalpartofbase;
  allpoints := MovedPoints(G.group);

  Print("#I extending\n");
  mp1 := [];
  i := 1;
  len := Length(mp);
  while i <= len and Length(mp[i][1]) <= max do
    if not IsSubset(fin,mp[i][2]) then
     Add(mp1, [Length(Difference(mp[i][2],fin)), mp[i][1], mp[i][2]]);
    fi;
    i := i + 1;
  od;
  mp := mp1;

  baselist := [ ];
  points := fin;
  if Length(fin) > 0 then
    Add(baselist, ["finalpart", fin]);
  fi;

  while (Length(mp) > 0 and points <> allpoints) do
    Print(Length(mp), "\c");
    min := Minimum(mp);
    Add(baselist, [min[2],Difference(min[3], points)]);
    points := Union(points, min[3]);

    mp1 := [];
    for t in mp do
      len1 := Length(Difference(t[3], points));
      if len1 > 0 then
        Add(mp1, [len1, t[2], t[3]]);
      fi;
    od;

    mp := mp1;
  od;
  Print("\n");

  return baselist;
end;

refinebase := function ( G, baselist, wordlengths )
  local
    b,
    len,
    L,
    low, high,
    allpoints,
    x, j,
    mp,
    cp,
    points,
    oldpoints,
    p,
    pos,
    newbaselist,
    pts, i1, i,
    min,
    diff, diff1,
    m;

  if not IsPermGroup(G.group) then
    Error("usage: refinebase( <permgroup> , <baselist>, <range-of-int>");
  fi;

  if not IsList(baselist) then
    Error("uasge: refinebase( <permgroup> , <baselist> , <range-of-ints>)");
  fi;

  if not IsRange(wordlengths) then
    Error("usage: refinebase( <permgroup> , <baselist> , <range-of-int>)");
  fi;

  b := 1;
  j := 1;
  if baselist[1][1] = "finalpart" then
    j := j+1;
  fi;

  for i in [j..Length(baselist)] do
    len := Length(baselist[i][1]);
    if len > b then
      b := len;
    fi;
  od;

  if wordlengths[1] <= b then
    Error("words of length ", b, " are already considered in baselist");
  fi;

  if not IsBound(G.movedPointsList) then
    Error("G.movedPointsList is not present");
  fi;

  if ForAll(baselist, p -> p[1] = "finalpart" or Length(p[2]) = 1) then
    Print("#I baselist is maximal refined \n");
    return baselist;
  fi;

  allpoints := Union(List(baselist, x -> x[2]));
  if Set(allpoints) <> Set(MovedPoints(G.group)) then
    Error("moved points of G are missing in baselist");
  fi;

  low := PositionProperty(G.movedPointsList, p-> Length(p[1]) >= wordlengths[1]);
  high := PositionProperty(G.movedPointsList, p -> Length(p[1]) > wordlengths[Length(wordlengths)]);

  if low = fail then
    return baselist;
  fi;

  if high = fail then
    high := Length(G.movedPointsList) + 1;
  fi;

  L := [];
  if baselist[1][1] <> "finalpart" then
    Add(L, baselist[1]);
  fi;

  for i in [2..Length(baselist)] do
    Add(L, [baselist[i][1], Union(List([1..i],j -> baselist[j][2]))]);
  od;

  mp := Concatenation(L, G.movedPointsList{[low..high-1]});
  Print("#I number of candidates for refinement: ", high - low,"\n");

  cp := List(baselist, p -> []);
  for x in mp do
    i := 1;
    pts := baselist[1][2];
    while not IsSubset(pts, x[2]) do
      i := i + 1;
      pts := Union(pts, baselist[i][2]);
    od;
    Add(cp[i],x);
  od;

  points := [];
  oldpoints := [];
  newbaselist := [];
  for p in baselist do
    pos := Position(baselist, p);
    points := Union(points, p[2]);

    if Length(p[2]) = 1 or p[1] = "finalpart" then
      Add(newbaselist, p);
      oldpoints := points;
    else
      while oldpoints <> points do
        i1 := PositionProperty(cp[pos], p -> Length(Difference(p[2], oldpoints)) > 0);
        if i1 = fail then
          return "failure";
        fi;
        min := cp[pos][i1];
        diff := Difference(cp[pos][1][2], oldpoints);
        for i in [i1+1..Length(cp[pos])] do
          m := cp[pos][i];
          diff1 := Difference(m[2], oldpoints);
          if Length(diff1) > 0 and Length(diff1) <= Length(diff) then
            if [Length(diff1),m] < [Length(diff), min] then
              min := m;
              diff := diff1;
            fi;
          fi;
        od;
        Add(newbaselist, [min[1], diff]);
        oldpoints := Union(oldpoints, diff);
      od;
    fi;
  od;
  Print("#I length of baselist = ", Length(newbaselist), "\c");

  if ForAll(newbaselist, p -> p[1] = "finalpart" or Length(p[2]) = 1 ) then
    Print("#I baselist is maximal refined");
  fi;
  Print("\n");

  return newbaselist;
end;


findbase := function ( G, m , finalpartofbase)
  local
      L,
      max,
      j;

  Print("#I calculating initial baselist with words of length <= ", m,"\n");
  L := findbaseinitial(G,m, finalpartofbase);
  Print("#I length of caselist = ",Length(L),"\n");
  max := Length(G.movedPointsList[Length(G.movedPointsList)][1]);
  Print("#I refining baselist\n");
  for j in [m+1..max] do
    L := refinebase(G, L, [j]);
  od;

  return L;
end;

findbaseall := function ( G, finalpartofbase )
  local max, L, bl, stop, mp, j, i;

  max := Length(G.movedPointsList[Length(G.movedPointsList)][1]);
  L := [];
  i := 1;
  stop := false;
  while i <= max and not stop do
    Print("strategy ", i, "\n");
    Print("------------\n\n");
    Print("#I calculating initial baselist with words of length <= ", i, "\n");

    bl := findbaseinitial( G, i, finalpartofbase);

    if bl <> [] and ForAll(bl, p -> p[1] = "finalpart" or Length(p[2]) = 1) then
      stop := true;
    fi;

    Print("#I length of baselist = ", Length(bl), "\n");
    mp := G.movedPointsList;
    max := Length(mp[Length(mp)][1]);
    Print("#I refining baselist\n");

    for j in [i+1..max] do
      bl := refinebase( G, bl, [j]);
    od;
    Add(L,bl);
    i := i + 1;
    Print("\n");
  od;

  if i < max then
    Print("#I strategies ", i, " - ", max, " will produce the same result like the startegy ", i-1,"\n");
  fi;

  return L;
end;
