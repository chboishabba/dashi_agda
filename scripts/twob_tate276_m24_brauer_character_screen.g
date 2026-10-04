# Compare the convention-correct weight-two 2B Tate trace on every
# 2-regular M24 class with the actual degree-276 M24 duad permutation
# character.
#
# Source/table chain used by CTblLib:
#
#   M24 -> 2^11:M24 -> Co1
#                    ^
#                    | quotient
#             2^1+24.Co1 -> Monster
#
# For an odd-order M24 class h, the odd-order lift(s) in the 2B centralizer
# are found by their Co1 quotient class.  Multiplication by the central 2B
# involution z is performed inside the 2B-centralizer character table.  The
# resulting Monster class of z*h supplies the weight-two Monster trace.
#
# The repository's Tate-grading convention bridge is the separate source
# theorem identifying this weight-two z*h trace with the 276-dimensional
# Tate head Brauer trace.  This runtime screen checks the finite class/fusion
# equality only; it does not silently promote character equality to a
# canonical module isomorphism.

if LoadPackage("ctbllib") <> true then
  Error("CTblLib is required");
fi;

m24 := CharacterTable("M24");
m22d2 := CharacterTable("M22.2");
localM24 := CharacterTable("2^11:M24");
co1 := CharacterTable("Co1");
cent2B := CharacterTable("2^1+24.Co1");
monster := CharacterTable("M");

if ForAny([m24,m22d2,localM24,co1,cent2B,monster], x -> x = fail) then
  Error("required CTblLib character table is unavailable");
fi;

m22d2ToM24 := GetFusionMap(m22d2,m24);
m24ToLocal := GetFusionMap(m24,localM24);
localToCo1 := GetFusionMap(localM24,co1);
centToCo1 := GetFusionMap(cent2B,co1);
centToMonster := GetFusionMap(cent2B,monster);

if ForAny([m22d2ToM24,m24ToLocal,localToCo1,centToCo1,centToMonster], x -> x = fail) then
  Error("required stored class fusion is unavailable");
fi;

# The rank-three degree-276 M24 action has point stabilizer M22:2.
duad := InducedClassFunctionsByFusionMap(
  m22d2,m24,[TrivialCharacter(m22d2)],m22d2ToM24)[1];
if duad[1] <> 276 then
  Error("induced M22:2 -> M24 character does not have degree 276");
fi;

# V^natural_2 = 1 + 196883.
monster196883 := First(Irr(monster), chi -> chi[1] = 196883);
if monster196883 = fail then
  Error("could not locate the 196883-dimensional Monster irreducible");
fi;
monsterV2 := TrivialCharacter(monster) + monster196883;
if monsterV2[1] <> 196884 then
  Error("unexpected Monster weight-two character degree");
fi;

centOrders := OrdersClassRepresentatives(cent2B);
m24Orders := OrdersClassRepresentatives(m24);
centCentre := ClassPositionsOfCentre(cent2B);
zpos := First(centCentre, i -> centOrders[i] = 2);
if zpos = fail then
  Error("2B-centralizer table has no central involution class");
fi;
if centToMonster[zpos] <> 3 then
  # In the standard Monster table position 3 is 2B.  Fail closed if the
  # library changes this convention rather than silently using another class.
  Error("central involution of 2B centralizer does not fuse to Monster class position 3");
fi;

oddM24Positions := Filtered([1..Length(m24Orders)], i -> m24Orders[i] mod 2 = 1);
rows := [];
allTraceIndependent := true;
allMatch := true;

for i in oddM24Positions do
  localPos := m24ToLocal[i];
  co1Pos := localToCo1[localPos];

  # Odd-order lifts are the p-regular lifts relevant for the Brauer character.
  lifts := Filtered([1..Length(centOrders)], c ->
    centToCo1[c] = co1Pos and centOrders[c] = m24Orders[i]);

  if Length(lifts) = 0 then
    Error("no odd-order 2B-centralizer lift for an M24 2-regular class");
  fi;

  liftTraceRows := [];
  traceValues := [];
  for c in lifts do
    products := Filtered([1..Length(centOrders)], j ->
      ClassMultiplicationCoefficient(cent2B,zpos,c,j) <> 0);
    if Length(products) <> 1 then
      Error("central 2B multiplication did not determine a unique centralizer class");
    fi;
    zhPos := products[1];
    monsterPos := centToMonster[zhPos];
    tr := monsterV2[monsterPos];
    if not IsInt(tr) then
      Error("weight-two Monster trace is not integral on a selected class");
    fi;
    Add(traceValues,tr);
    Add(liftTraceRows,[c,zhPos,monsterPos,tr]);
  od;

  independent := Length(Set(traceValues)) = 1;
  if not independent then
    allTraceIndependent := false;
  fi;

  tateTrace := traceValues[1];
  duadTrace := duad[i];
  matches := independent and tateTrace = duadTrace;
  if not matches then
    allMatch := false;
  fi;

  Add(rows,[i,m24Orders[i],localPos,co1Pos,duadTrace,tateTrace,
            Length(lifts),independent,matches,liftTraceRows]);
od;

PrintBool := function(out,b)
  if b then AppendTo(out,"true"); else AppendTo(out,"false"); fi;
end;

PrintIntList := function(out,xs)
  local j;
  AppendTo(out,"[");
  for j in [1..Length(xs)] do
    if j>1 then AppendTo(out,","); fi;
    AppendTo(out,String(xs[j]));
  od;
  AppendTo(out,"]");
end;

PrintLiftRows := function(out,xss)
  local j;
  AppendTo(out,"[");
  for j in [1..Length(xss)] do
    if j>1 then AppendTo(out,","); fi;
    PrintIntList(out,xss[j]);
  od;
  AppendTo(out,"]");
end;

output := OutputTextFile("build/twob_tate276_m24_brauer_character_screen.json",false);
SetPrintFormattingStatus(output,false);
AppendTo(output,"{\n");
AppendTo(output,"  \"m24_order\": ",String(Size(m24)),",\n");
AppendTo(output,"  \"duad_degree\": ",String(duad[1]),",\n");
AppendTo(output,"  \"monster_v2_degree\": ",String(monsterV2[1]),",\n");
AppendTo(output,"  \"central_2b_class_position\": ",String(zpos),",\n");
AppendTo(output,"  \"central_2b_monster_class_position\": ",String(centToMonster[zpos]),",\n");
AppendTo(output,"  \"two_regular_class_count\": ",String(Length(oddM24Positions)),",\n");
AppendTo(output,"  \"all_lift_traces_independent\": "); PrintBool(output,allTraceIndependent); AppendTo(output,",\n");
AppendTo(output,"  \"all_two_regular_traces_match_duad276\": "); PrintBool(output,allMatch); AppendTo(output,",\n");
AppendTo(output,"  \"rows\": [\n");
for r in [1..Length(rows)] do
  row := rows[r];
  AppendTo(output,"    {\"m24_class_position\":",String(row[1]),
    ",\"order\":",String(row[2]),
    ",\"local_m24_class_position\":",String(row[3]),
    ",\"co1_class_position\":",String(row[4]),
    ",\"duad_trace\":",String(row[5]),
    ",\"tate_trace_candidate\":",String(row[6]),
    ",\"odd_lift_count\":",String(row[7]),
    ",\"lift_trace_independent\":");
  PrintBool(output,row[8]);
  AppendTo(output,",\"matches\":"); PrintBool(output,row[9]);
  AppendTo(output,",\"lift_rows\":"); PrintLiftRows(output,row[10]);
  AppendTo(output,"}");
  if r < Length(rows) then AppendTo(output,","); fi;
  AppendTo(output,"\n");
od;
AppendTo(output,"  ]\n}\n");
CloseStream(output);

Print("2B Tate-276 / M24 duad Brauer-character screen: classes=",
  Length(oddM24Positions),
  "; lift-independent=",allTraceIndependent,
  "; all-match=",allMatch,"\n");
QUIT;
