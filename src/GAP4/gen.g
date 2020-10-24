# encode the counters as hexadecimal characters.
initialState := ['0','1','2','3','4','5','6','7','8','9','A','B','C'];

# basically finds the index of a given element
#  copied off of Sebastian Egner

find_k := function( state, c )
  local k;
  for k in [1,2..13] do
    if state[k] = c then
      return k;
    fi;
  od;
  return false;
end;

# Declaring the lines in P^{2}(FF_{3}) as per Noam Elkies scheme

lines := [[1,2,3,4],[1,5,6,7],[1,10,11,12],[1,8,9,13],
[2,5,9,10],[2,7,8,12],[2,6,11,13],[3,5,12,13],[3,7,9,11],[3,6,8,10],[4,5,8,11],[4,6,9,12],[4,7,10,13]];

# Defining puzzle movement

move := function( state, c)
  local stateNew, holeVal, pushVal, i, tempSet, temp;
  stateNew := ShallowCopy(state);

  holeVal := find_k(state,'0');
  pushVal := find_k(state,c);

  stateNew[holeVal] := c;
  stateNew[pushVal] := '0';

  for i in [1,2..13] do
    if holeVal in lines[i] and pushVal in lines[i] then
      tempSet := ShallowCopy(lines[i]);
      RemoveSet(tempSet, holeVal);
      RemoveSet(tempSet,pushVal);
      temp := stateNew[tempSet[2]];
      stateNew[tempSet[2]] := stateNew[tempSet[1]];
      stateNew[tempSet[1]] := temp;
      break;
    fi;
  od;

  return stateNew;
end;

# Collecting all stabilizing moves of the form push A, push B, push A from the initialState
#  Copied from Sebastion Egner

allowedPush := ['1','2','3','4','5','6','7','8','9','A','B','C'];

conjugateABA := function ()
  local moveGen, A, B, temp;
  moveGen := [];

  for A in [1,2..12] do
    for B in [1,2..12] do
      temp := move(move(move(initialState,allowedPush[A]), allowedPush[B]), allowedPush[A]);
      if A <> B and temp[1] = '0' then
        temp := PermList(List(temp, si-> Position(initialState,si)));
        if not ForAny(moveGen,mi->mi[1]=temp) then
          Add(moveGen,[temp,[A,B,A]]);
        fi;
      fi;
    od;
  od;
  return moveGen;
end;

conjugateABA := conjugateABA();

# create the M12 group using these stabilizing groups
# The collection of all moves the stabilize the hole of the puzzle is the M12 group
#  Again stolen from Sebastian Egner
#  Some GAP3 code has been ported

M12 := Group(List(conjugateABA,x->x[1]),());

nameList := [];
for i in [1..Length(conjugateABA)] do
  Add(nameList,Concatenation(['g'],String(i)));
od;

moveUnderneathM12 := List(conjugateABA,c->[c[2][1],c[2][2],0]);

M12Rec := rec();                                          # Encompassing record
M12Rec.group := M12;                                      # underlying group
M12Rec.moves := Set(moveUnderneathM12);                   # generators of stabilizer
M12Rec.abstractGenerators := GeneratorsOfGroup(FreeGroup(nameList));                    # just the abstract generators
M12Rec.base := BaseStabChain(StabChain(M12Rec.group));   # get the base points of the topmost record
M12Rec.generators := List(conjugateABA,x->x[1]);


# naive search
search := function ( )
  local shortest, agenda, s, w, agendaInc, m, i, sm, wm;

  shortest := [];
  agenda := [[['0','1','2','3','4','5','6','7','8','9','A','B','C'],[]]];

  while Length(agenda) > 0 do
    if Length(shortest) = 1000 then
      return;
    fi;

    s := agenda[1][1];
    w := agenda[1][2];
    agenda := agenda{[2..Length(agenda)]};
    agendaInc := [];
    for m in [1..12] do
      sm := move(s,allowedPush[m]);
      i := Position(shortest,sw -> sw[1] = sm);
      if i = fail then
        wm := ShallowCopy(w);
        Add(wm, m);
        Add(shortest, [sm, wm]);
        Add(agendaInc, [sm, wm]);
      fi;
    od;
    Append(agenda, agendaInc);
    Print(agenda);
  od;

  return shortest;
end;

Read("strats.g");
AbstractStabChainGenerationAllStrategies(M12Rec, 10000, []);
Read("StratPy.g");
PrintASCToPy("C:/Users/User/Downloads/M13/out.sgs", GetASC(M12Rec));
