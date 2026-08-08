# Exact CTblLib restriction of the 196883-dimensional Monster character
# to the 3B normalizer.  The computation fails closed if the tables,
# stored fusion, character, integral decomposition, classwise reconstruction,
# or central 3B class cannot be recovered.
#
# PRIMARY COMPUTATIONAL SOURCE
# Thomas Breuer, "The GAP Character Table Library", CTblLib 1.3.11 (2025).
# Package documentation; no DOI asserted.
#
# PRIMARY MATHEMATICAL SOURCE
# R. W. Barraclough and R. A. Wilson,
# "The Character Table of a Maximal Subgroup of the Monster",
# LMS Journal of Computation and Mathematics 10 (2007), 161--175.
# DOI: 10.1112/S1461157000001352.
#
# Run with:
#   mkdir -p build
#   gap -q scripts/monster_3b_normalizer_restriction.g

LoadPackage("ctbllib");

monster := CharacterTable("M");
mn3b := CharacterTable("MN3B");
if mn3b = fail then
  mn3b := CharacterTable("3^(1+12).2.Suz.2");
fi;
if mn3b = fail then
  mn3b := CharacterTable("3^1+12.2.Suz.2");
fi;

if monster = fail then
  Error("CTblLib does not provide CharacterTable(\"M\")");
fi;
if mn3b = fail then
  Error("CTblLib does not provide the MN3B character table");
fi;

monsterIrr := Irr(monster);
positions := Filtered([1..Length(monsterIrr)],
  i -> monsterIrr[i][1] = 196883);
if Length(positions) <> 1 then
  Error("expected exactly one Monster irreducible of degree 196883");
fi;
chiPosition := positions[1];
chi := monsterIrr[chiPosition];

fusion := GetFusionMap(mn3b, monster);
if fusion = fail then
  Error("stored MN3B -> M class fusion is unavailable");
fi;

restrictedValues := List(fusion, i -> chi[i]);
restricted := ClassFunction(mn3b, restrictedValues);
mn3bIrr := Irr(mn3b);
multiplicities := List(mn3bIrr,
  psi -> ScalarProduct(mn3b, restricted, psi));

if ForAny(multiplicities, x -> not IsInt(x) or x < 0) then
  Error("restriction did not decompose with nonnegative integral multiplicities");
fi;

nonzero := Filtered([1..Length(multiplicities)],
  i -> multiplicities[i] <> 0);
reconstructedDegree := Sum(nonzero,
  i -> multiplicities[i] * mn3bIrr[i][1]);
if reconstructedDegree <> 196883 then
  Error("restriction decomposition does not reconstruct degree 196883");
fi;

reconstructedValues := List([1..Length(restrictedValues)], c ->
  Sum(nonzero, i -> multiplicities[i] * mn3bIrr[i][c]));
classwiseReconstruction := reconstructedValues = restrictedValues;
if not classwiseReconstruction then
  Error("restriction constituents do not reconstruct every MN3B class value");
fi;

monsterClassNames := AtlasClassNames(monster);
monster3BPosition := Position(monsterClassNames, "3B");
if monster3BPosition = fail then
  Error("Monster table does not expose the ATLAS class name 3B");
fi;

mn3bOrders := OrdersClassRepresentatives(mn3b);
mn3bClassSizes := SizesConjugacyClasses(mn3b);
central3BCandidates := Filtered([1..Length(fusion)], i ->
  fusion[i] = monster3BPosition
  and mn3bOrders[i] = 3
  and mn3bClassSizes[i] = 2);
if Length(central3BCandidates) <> 1 then
  Error("expected one size-two MN3B class of order three fusing to Monster 3B");
fi;
central3BClass := central3BCandidates[1];
threeBTrace := restrictedValues[central3BClass];
if threeBTrace <> 53 then
  Error("the degree-196883 Monster character does not have trace 53 on 3B");
fi;

nontrivialNumerator := 196883 - threeBTrace;
if nontrivialNumerator mod 3 <> 0 then
  Error("(degree - 3B trace) is not divisible by three");
fi;
nontrivialMultiplicity := nontrivialNumerator / 3;
invariantMultiplicity := nontrivialMultiplicity + threeBTrace;
if nontrivialMultiplicity <> 65610 then
  Error("unexpected nontrivial 3B eigenspace multiplicity");
fi;
if invariantMultiplicity <> 65663 then
  Error("unexpected invariant 3B eigenspace multiplicity");
fi;
if invariantMultiplicity + 2 * nontrivialMultiplicity <> 196883 then
  Error("3B eigenspace multiplicities do not reconstruct dimension");
fi;

records := List(nonzero, i -> rec(
  position := i,
  multiplicity := multiplicities[i],
  degree := mn3bIrr[i][1],
  contribution := multiplicities[i] * mn3bIrr[i][1]
));

output := OutputTextFile("build/monster_3b_normalizer_restriction.json", false);
SetPrintFormattingStatus(output, false);
PrintTo(output,
  "{\n",
  "  \"ctbllib_table\": \"", Identifier(mn3b), "\",\n",
  "  \"source_table\": \"", Identifier(monster), "\",\n",
  "  \"target_table\": \"", Identifier(mn3b), "\",\n",
  "  \"monster_character_position\": ", chiPosition, ",\n",
  "  \"monster_character_degree\": 196883,\n",
  "  \"source_class_count\": ", Length(fusion), ",\n",
  "  \"classwise_reconstruction\": true,\n",
  "  \"reconstructed_degree\": ", reconstructedDegree, ",\n",
  "  \"monster_3b_class_position\": ", monster3BPosition, ",\n",
  "  \"mn3b_central_3b_class_position\": ", central3BClass, ",\n",
  "  \"mn3b_central_3b_class_size\": 2,\n",
  "  \"three_b_trace\": ", threeBTrace, ",\n",
  "  \"invariant_multiplicity\": ", invariantMultiplicity, ",\n",
  "  \"zeta_multiplicity\": ", nontrivialMultiplicity, ",\n",
  "  \"zeta_squared_multiplicity\": ", nontrivialMultiplicity, ",\n",
  "  \"constituents\": [\n"
);

for j in [1..Length(records)] do
  r := records[j];
  PrintTo(output,
    "    {\"position\": ", r.position,
    ", \"multiplicity\": ", r.multiplicity,
    ", \"degree\": ", r.degree,
    ", \"contribution\": ", r.contribution, "}"
  );
  if j < Length(records) then
    PrintTo(output, ",");
  fi;
  PrintTo(output, "\n");
od;

PrintTo(output, "  ]\n}\n");
CloseStream(output);

Print("MN3B restriction written to build/monster_3b_normalizer_restriction.json\n");
Print("Nonzero constituents: ", Length(records), "\n");
Print("Classwise reconstruction: true\n");
Print("3B multiplicities: ", invariantMultiplicity, ", ",
  nontrivialMultiplicity, ", ", nontrivialMultiplicity, "\n");
QUIT;
