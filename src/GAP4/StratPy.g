

GetASC := function ( G )
  local Grp, R, A, T, level, points, wx, p;
  if not IsBound(G.abstractStabChain) then
    Error("<G> must have a stable chain");
  fi;
  Grp := G.group;
  A := G.abstractStabChain;

  R := rec();

  R.nrPoints := LargestMovedPoint(Grp);
  R.basepoints := A.base;

  R.generators := G.generators;
  R.abstractGenerators := G.abstractGenerators;
  R.transversals := [];
  R.words := [];
  R.groups := Grp;
  for level in [1..Length(R.basepoints)] do
    R.transversals[level] := List([1..R.nrPoints],p->false);
    R.words[level] := List([1..R.nrPoints],p->false);
    for wx in ASCOps.TransversalOrbitGraph(G, level) do
      p:= R.basepoints[level]^wx[2];
      R.transversals[level][p] := wx[2];
      R.words[level][p] := wx[1];
    od;
  od;
  return R;
end;

PrintASCToPy := function ( filename, R )
  local print, printListInLine, printList;

  printListInLine := function ( x, print )
    local i;

    Print("(");
    for i in [1..Length(x)] do
      print(x[i]);
      if i < Length(x) then
        Print(", ");
      fi;
    od;
    Print(")");
  end;
  printList := function( x, print, indent)
    local i, k;
    Print("[");
    for i in [1..Length(x)] do
      print(x[i]);
      if i<Length(x) then
        Print(",\n");
        for k in [1..indent+2] do
          Print(" ");
        od;
      fi;
    od;
    Print("\n");
    for k in [1..indent] do
      Print(" ");
    od;
    Print("]");
  end;

  print := function ( R )
    local ags, agsInv;
    ags := R.abstractGenerators;
    agsInv := List(ags, g->g^-1);

    Print("nrPoints = ", R.nrPoints, "\n\n");
    Print("nrBasepoints = ", Length(R.basepoints), "\n");
    Print("basepoints = ");
    printListInLine(R.basepoints-1, Print);
    Print("\n\n");
    Print("NrGenerators = ", Length(R.generators),"\n");
    Print("generators = \n");
    printList(
    R.generators,
    function ( perm )
      printListInLine(
      OnTuples([1..R.nrPoints],perm)-1,
      Print
      );
    end,
    2
    );
    Print("\n\n");

    Print("transversals = \n");
    printList(
      R.transversals,
      function ( t )
        printList(
          t,
          function ( perm )
            if perm = false then
              printListInLine(
                List([1..R.nrPoints],i->-1),
                Print
              );
            else
              printListInLine(
                OnTuples([1..R.nrPoints],perm)-1,
                Print
              );
            fi;
          end,
          4
        );
      end,
      2
    );
    Print("\n\n");

    Print("words =\n");
    printList(
      R.words,
      function ( t )
        printList(
          t,
          function ( word )
            local w, i, wi;
            w:= [ ];
            if word <> false then
              for i in [1..Length(word)] do
                wi:= Subword(word, i, i);
                if wi in ags then
                  Add(w, Position(ags,wi));
                elif wi in agsInv then
                  Add(w, -Position(agsInv,wi));
                else
                  Error("<wi> not in <R>.abstractGenerators");
                fi;
              od;
            fi;
            Add(w,0);
            printListInLine(w,Print);
          end,
          4
        );
      end,
      2
    );
    Print("\n\n");
    return "";
  end;

  if IsPermGroup(R) then
    R := GetASC(R);
  fi;

  LogTo(filename);
  print(R);
end;
