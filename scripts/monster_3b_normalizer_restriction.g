# Exact CTblLib restriction of the 196883-dimensional Monster character
# to the 3B normalizer.  The computation fails closed if the tables,
# stored fusion, character, integral decomposition, classwise reconstruction,
# central 3B class, normal extraspecial kernel class carrier, or Clifford
# constituent split cannot be recovered.
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

monsterClassNames := ClassNames(monster, "ATLAS");
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

# Recover the actual normal extraspecial kernel E from the ordinary character
# table as the unique normal class union of order 3^13.  This certifies the
# complete MN3B class carrier of E.  Phase resolution is handled below at the
# irreducible-constituent level by the central 3B trace ratio.
kernelOrder := 3^13;
normalClassSets := ClassPositionsOfNormalSubgroups(mn3b);
kernelCandidates := Filtered(normalClassSets, classes ->
  Sum(classes, i -> mn3bClassSizes[i]) = kernelOrder);
if Length(kernelCandidates) <> 1 then
  Error("expected one normal MN3B class union of order 3^13");
fi;
kernelClasses := kernelCandidates[1];
if not 1 in kernelClasses then
  Error("extraspecial kernel class carrier does not contain the identity");
fi;
if not central3BClass in kernelClasses then
  Error("extraspecial kernel class carrier does not contain the central 3B class");
fi;

kernelClassSizeSum := Sum(kernelClasses, i -> mn3bClassSizes[i]);
if kernelClassSizeSum <> kernelOrder then
  Error("extraspecial kernel class sizes do not sum to 3^13");
fi;

kernelOrders := Set(List(kernelClasses, i -> mn3bOrders[i]));
if ForAny(kernelOrders, order -> not order in [1, 3]) then
  Error("extraspecial kernel class carrier contains an element order other than 1 or 3");
fi;

if ForAny(kernelClasses, i -> not IsInt(restrictedValues[i])) then
  Error("expected integral Monster character values on all extraspecial kernel classes");
fi;

kernelInvariantNumerator := Sum(kernelClasses,
  i -> mn3bClassSizes[i] * restrictedValues[i]);
if not IsInt(kernelInvariantNumerator) then
  Error("extraspecial-kernel character average numerator is not integral");
fi;
if kernelInvariantNumerator mod kernelOrder <> 0 then
  Error("extraspecial-kernel character average is not an integer");
fi;
kernelInvariantDimension := kernelInvariantNumerator / kernelOrder;
if not IsInt(kernelInvariantDimension) or kernelInvariantDimension < 0 then
  Error("extraspecial-kernel invariant dimension is not a nonnegative integer");
fi;

kernelClassRecords := List(kernelClasses, i -> rec(
  position := i,
  size := mn3bClassSizes[i],
  order := mn3bOrders[i],
  trace := restrictedValues[i]
));

# Clifford classification at the size-two central 3B orbit.
#
# A constituent lying over an E-character with trivial central character has
# chi(z)=chi(1).  A constituent induced from the normalizer orbit
# {H_zeta,H_zeta^2} has equal zeta/zeta^2 halves and hence
#
#   chi(z) = (degree/2)(zeta+zeta^2) = -degree/2.
#
# Thus the actual MN3B character table itself separates the fixed sector from
# the paired nontrivial phase sector without choosing a Monster basis.
centreTrivialConstituents := [];
phasePairConstituents := [];
for i in nonzero do
  constituentDegree := mn3bIrr[i][1];
  centralValue := mn3bIrr[i][central3BClass];
  if not IsInt(centralValue) then
    Error("a nonzero MN3B constituent has nonintegral central 3B trace");
  fi;
  if centralValue = constituentDegree then
    Add(centreTrivialConstituents, i);
  elif 2 * centralValue = -constituentDegree then
    Add(phasePairConstituents, i);
  else
    Error("a nonzero MN3B constituent has neither fixed nor paired-phase central trace ratio");
  fi;
od;

centreTrivialDegreeTotal := Sum(centreTrivialConstituents,
  i -> multiplicities[i] * mn3bIrr[i][1]);
phasePairDegreeTotal := Sum(phasePairConstituents,
  i -> multiplicities[i] * mn3bIrr[i][1]);

if centreTrivialDegreeTotal <> invariantMultiplicity then
  Error("centre-trivial constituent degrees do not reconstruct the invariant sector");
fi;
if phasePairDegreeTotal <> 2 * nontrivialMultiplicity then
  Error("paired-phase constituent degrees do not reconstruct both nontrivial sectors");
fi;
if centreTrivialDegreeTotal + phasePairDegreeTotal <> 196883 then
  Error("Clifford constituent split does not reconstruct the Monster degree");
fi;

heisenbergPairDegree := 2 * 729;
phasePairRecords := [];
phaseMultiplicityDegrees := [];
for i in phasePairConstituents do
  constituentDegree := mn3bIrr[i][1];
  if constituentDegree mod heisenbergPairDegree <> 0 then
    Error("paired-phase constituent degree is not divisible by 2*729");
  fi;
  multiplicityDegree := constituentDegree / heisenbergPairDegree;
  Add(phasePairRecords, rec(
    position := i,
    multiplicity := multiplicities[i],
    degree := constituentDegree,
    centralTrace := mn3bIrr[i][central3BClass],
    multiplicityDegree := multiplicityDegree,
    contribution := multiplicities[i] * constituentDegree
  ));
  for copy in [1..multiplicities[i]] do
    Add(phaseMultiplicityDegrees, multiplicityDegree);
  od;
od;

Sort(phaseMultiplicityDegrees);
if phaseMultiplicityDegrees <> [12, 78] then
  Error("actual paired-phase multiplicity degrees are not exactly 12 and 78");
fi;
if Sum(phaseMultiplicityDegrees) <> 90 then
  Error("actual paired-phase multiplicity degrees do not sum to 90");
fi;

twelvePlusSeventyEightCertified := true;

records := [];
for i in nonzero do
  if i in centreTrivialConstituents then
    cliffordType := "centre-trivial";
  else
    cliffordType := "paired-phase";
  fi;
  Add(records, rec(
    position := i,
    multiplicity := multiplicities[i],
    degree := mn3bIrr[i][1],
    centralTrace := mn3bIrr[i][central3BClass],
    cliffordType := cliffordType,
    contribution := multiplicities[i] * mn3bIrr[i][1]
  ));
od;

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
  "  \"extraspecial_kernel_order\": ", kernelOrder, ",\n",
  "  \"extraspecial_kernel_class_count\": ", Length(kernelClasses), ",\n",
  "  \"extraspecial_kernel_class_size_sum\": ", kernelClassSizeSum, ",\n",
  "  \"extraspecial_kernel_contains_central_3b\": true,\n",
  "  \"extraspecial_kernel_all_nonidentity_orders_three\": true,\n",
  "  \"extraspecial_kernel_invariant_numerator\": ", kernelInvariantNumerator, ",\n",
  "  \"extraspecial_kernel_invariant_dimension\": ", kernelInvariantDimension, ",\n",
  "  \"centre_trivial_constituent_degree_total\": ", centreTrivialDegreeTotal, ",\n",
  "  \"phase_pair_constituent_degree_total\": ", phasePairDegreeTotal, ",\n",
  "  \"phase_pair_heisenberg_degree\": ", heisenbergPairDegree, ",\n",
  "  \"phase_pair_multiplicity_degrees\": [12, 78],\n",
  "  \"twelve_plus_seventy_eight_certified\": true,\n",
  "  \"extraspecial_kernel_class_positions\": ["
);
for j in [1..Length(kernelClasses)] do
  PrintTo(output, kernelClasses[j]);
  if j < Length(kernelClasses) then
    PrintTo(output, ", ");
  fi;
od;
PrintTo(output, "],\n  \"extraspecial_kernel_classes\": [\n");
for j in [1..Length(kernelClassRecords)] do
  r := kernelClassRecords[j];
  PrintTo(output,
    "    {\"position\": ", r.position,
    ", \"size\": ", r.size,
    ", \"order\": ", r.order,
    ", \"trace\": ", r.trace, "}"
  );
  if j < Length(kernelClassRecords) then
    PrintTo(output, ",");
  fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ],\n  \"phase_pair_constituents\": [\n");
for j in [1..Length(phasePairRecords)] do
  r := phasePairRecords[j];
  PrintTo(output,
    "    {\"position\": ", r.position,
    ", \"multiplicity\": ", r.multiplicity,
    ", \"degree\": ", r.degree,
    ", \"central_trace\": ", r.centralTrace,
    ", \"multiplicity_degree\": ", r.multiplicityDegree,
    ", \"contribution\": ", r.contribution, "}"
  );
  if j < Length(phasePairRecords) then
    PrintTo(output, ",");
  fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ],\n  \"constituents\": [\n");

for j in [1..Length(records)] do
  r := records[j];
  PrintTo(output,
    "    {\"position\": ", r.position,
    ", \"multiplicity\": ", r.multiplicity,
    ", \"degree\": ", r.degree,
    ", \"central_trace\": ", r.centralTrace,
    ", \"clifford_type\": \"", r.cliffordType, "\"",
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
Print("Extraspecial kernel order: ", kernelOrder,
  "; MN3B class count: ", Length(kernelClasses), "\n");
Print("Extraspecial-kernel invariant dimension: ",
  kernelInvariantDimension, "\n");
Print("Clifford totals: fixed ", centreTrivialDegreeTotal,
  "; paired phases ", phasePairDegreeTotal, "\n");
Print("Actual phase multiplicity degrees: 12, 78\n");
QUIT;
