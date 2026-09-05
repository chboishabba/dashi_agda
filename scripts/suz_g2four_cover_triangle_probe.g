# CTblLib probe for the G2(4) spine behind the Wilson 12/78/143 triangle.
#
# Tests three distinct restriction problems:
#   Suz      -> G2(4)        on every degree-143 irrep;
#   3.Suz    -> 3xG2(4)     on every degree-78 irrep;
#   6.Suz    -> 3x2.G2(4)   on every degree-12 irrep.
#
# It then pushes every restricted 3.Suz degree-78 class function one level
# farther down the stored G2(4) -> 3xG2(4) fusion and compares it class-by-class
# with the degree-78 constituent extracted from every exact
#   Suz_143 | G2(4) = 65 + 78
# branch.  This is the first same-G2 class-function weld test; equality of
# degrees alone is never accepted.

LoadPackage("ctbllib");

FetchTable := function(name)
  local t;
  t := CharacterTable(name);
  if t = fail then
    Error(Concatenation("CTblLib does not provide CharacterTable(\"", name, "\")"));
  fi;
  return t;
end;

RestrictDegreeFamily := function(source, target, degree)
  local fusion, srcIrr, tgtIrr, positions, records, p, chi, vals, res, mults, nz, recdeg;
  fusion := GetFusionMap(target, source);
  if fusion = fail then
    Error(Concatenation("stored fusion ", Identifier(target), " -> ", Identifier(source), " unavailable"));
  fi;
  srcIrr := Irr(source);
  tgtIrr := Irr(target);
  positions := Filtered([1..Length(srcIrr)], i -> srcIrr[i][1] = degree);
  if Length(positions) = 0 then
    Error(Concatenation("no source irreducible of requested degree ", String(degree), " in ", Identifier(source)));
  fi;
  records := [];
  for p in positions do
    chi := srcIrr[p];
    vals := List(fusion, c -> chi[c]);
    res := ClassFunction(target, vals);
    mults := List(tgtIrr, psi -> ScalarProduct(target, res, psi));
    if ForAny(mults, x -> not IsInt(x) or x < 0) then
      Error("restriction multiplicities are not nonnegative integers");
    fi;
    nz := Filtered([1..Length(mults)], i -> mults[i] <> 0);
    recdeg := Sum(nz, i -> mults[i] * tgtIrr[i][1]);
    if recdeg <> degree then
      Error("restriction does not reconstruct requested degree");
    fi;
    Add(records, rec(
      sourcePosition := p,
      targetPositions := nz,
      degrees := List(nz, i -> tgtIrr[i][1]),
      multiplicities := List(nz, i -> mults[i]),
      reconstructedDegree := recdeg,
      restrictedValues := vals
    ));
  od;
  return records;
end;

RestrictStoredValues := function(source, target, valuesOnSource)
  local fusion;
  fusion := GetFusionMap(target, source);
  if fusion = fail then
    Error(Concatenation("stored fusion ", Identifier(target), " -> ", Identifier(source), " unavailable"));
  fi;
  return List(fusion, c -> valuesOnSource[c]);
end;

suz := FetchTable("Suz");
g24 := FetchTable("G2(4)");
threeSuz := FetchTable("3.Suz");
threeG24 := FetchTable("3xG2(4)");
sixSuz := FetchTable("6.Suz");
threeTwoG24 := FetchTable("3x2.G2(4)");

suz143 := RestrictDegreeFamily(suz, g24, 143);
threeSuz78 := RestrictDegreeFamily(threeSuz, threeG24, 78);
sixSuz12 := RestrictDegreeFamily(sixSuz, threeTwoG24, 12);

# Exact branching predicate for the ordinary Suz 143 restriction.
Suz143Is65Plus78 := function(r)
  local pairs;
  if Length(r.degrees) <> 2 then return false; fi;
  pairs := List([1..Length(r.degrees)], i -> [r.degrees[i], r.multiplicities[i]]);
  Sort(pairs);
  return pairs = [ [65,1], [78,1] ];
end;

# Extract the literal G2(4) irreducible position corresponding to the unique
# degree-78 constituent of an exact 65+78 branch record.
G2SeventyEightPosition := function(r)
  local i;
  if not Suz143Is65Plus78(r) then return fail; fi;
  i := Position(r.degrees, 78);
  if i = fail then return fail; fi;
  return r.targetPositions[i];
end;

# Class-function weld matrix.  Each row compares one exact Suz143->G2(4)
# degree-78 constituent against one 3.Suz78->3xG2(4) restriction pushed farther
# down to the same ordinary G2(4) table.
g2Irr := Irr(g24);
weldComparisons := [];
for sr in suz143 do
  g2pos := G2SeventyEightPosition(sr);
  if g2pos <> fail then
    suz78Values := ValuesOfClassFunction(g2Irr[g2pos]);
    for tr in threeSuz78 do
      cover78DownToG2Values := RestrictStoredValues(threeG24, g24, tr.restrictedValues);
      Add(weldComparisons, rec(
        suz143SourcePosition := sr.sourcePosition,
        g2SeventyEightPosition := g2pos,
        threeSuz78SourcePosition := tr.sourcePosition,
        sameG2ClassFunction := suz78Values = cover78DownToG2Values
      ));
    od;
  fi;
od;

output := OutputTextFile("build/suz_g2four_cover_triangle_probe.json", false);
SetPrintFormattingStatus(output, false);
PrintTo(output, "{\n");
PrintTo(output, "  \"suz_to_g2_4_degree143\": [\n");
for j in [1..Length(suz143)] do
  r := suz143[j];
  PrintTo(output,
    "    {\"source_position\": ", r.sourcePosition,
    ", \"degrees\": ", r.degrees,
    ", \"multiplicities\": ", r.multiplicities,
    ", \"is_exact_65_plus_78\": ", LowercaseString(String(Suz143Is65Plus78(r))), "}"
  );
  if j < Length(suz143) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ],\n");

PrintTo(output, "  \"three_suz_to_three_x_g2_4_degree78\": [\n");
for j in [1..Length(threeSuz78)] do
  r := threeSuz78[j];
  PrintTo(output,
    "    {\"source_position\": ", r.sourcePosition,
    ", \"degrees\": ", r.degrees,
    ", \"multiplicities\": ", r.multiplicities, "}"
  );
  if j < Length(threeSuz78) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ],\n");

PrintTo(output, "  \"six_suz_to_three_x_two_g2_4_degree12\": [\n");
for j in [1..Length(sixSuz12)] do
  r := sixSuz12[j];
  PrintTo(output,
    "    {\"source_position\": ", r.sourcePosition,
    ", \"degrees\": ", r.degrees,
    ", \"multiplicities\": ", r.multiplicities, "}"
  );
  if j < Length(sixSuz12) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ],\n");

PrintTo(output, "  \"g2_4_degree78_class_function_welds\": [\n");
for j in [1..Length(weldComparisons)] do
  r := weldComparisons[j];
  PrintTo(output,
    "    {\"suz143_source_position\": ", r.suz143SourcePosition,
    ", \"g2_78_position\": ", r.g2SeventyEightPosition,
    ", \"three_suz78_source_position\": ", r.threeSuz78SourcePosition,
    ", \"same_g2_class_function\": ", LowercaseString(String(r.sameG2ClassFunction)), "}"
  );
  if j < Length(weldComparisons) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ]\n}\n");
CloseStream(output);

Print("G2(4) cover-triangle probe written to build/suz_g2four_cover_triangle_probe.json\n");
Print("Exact G2(4) degree-78 class-function comparisons: ", Length(weldComparisons), "\n");
QUIT_GAP(0);
