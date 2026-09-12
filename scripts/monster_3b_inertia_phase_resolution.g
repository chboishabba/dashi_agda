# Phase-resolve the paired nontrivial 3B-normalizer constituents by restricting
# from N(3B)=3^(1+12).2.Suz.2 to the centralizer/inertia subgroup
# C_M(3B)=3^(1+12).2.Suz.
#
# This is deliberately fail-closed.  It does not assume that CTblLib exposes
# the required inertia table or a unique fusion.  If those data are absent,
# ambiguous, or fail the expected Clifford-theory checks, the script aborts.
#
# PRIMARY MATHEMATICAL SOURCE
# R. W. Barraclough and R. A. Wilson,
# "The Character Table of a Maximal Subgroup of the Monster",
# LMS J. Comput. Math. 10 (2007), 161--175.
# DOI: 10.1112/S1461157000001352.
#
# CHARACTER-THEORY SOURCE
# I. M. Isaacs, "Character Theory of Finite Groups", 1976/1994 reprint.
# ISBN 978-0-486-68014-9; no DOI asserted.
#
# COMPUTATIONAL SOURCE
# Thomas Breuer, GAP Character Table Library documentation; no DOI asserted.

if LoadPackage("ctbllib") <> true then
  Error("CTblLib is required");
fi;

mn3b := CharacterTable("MN3B");
if mn3b = fail then
  Error("MN3B character table is unavailable");
fi;

# Try canonical spellings for the 3B centralizer/inertia table.
inertiaNames := [
  "3^(1+12).2.Suz",
  "3^1+12.2.Suz",
  "3^(1+12):2.Suz",
  "3^1+12:2.Suz"
];
inertia := fail;
inertiaName := fail;
for name in inertiaNames do
  candidate := CharacterTable(name);
  if candidate <> fail then
    inertia := candidate;
    inertiaName := name;
    break;
  fi;
od;
if inertia = fail then
  Error("CTblLib does not expose a tested 3B inertia/centralizer table name");
fi;

# Obtain an inertia -> MN3B class fusion.  Prefer stored data; otherwise require
# exactly one possible fusion so no arbitrary choice is made.
fusion := GetFusionMap(inertia, mn3b);
if fusion = fail then
  possibleFusions := PossibleClassFusions(inertia, mn3b);
  if Length(possibleFusions) <> 1 then
    Error("inertia -> MN3B class fusion is unavailable or non-unique");
  fi;
  fusion := possibleFusions[1];
fi;

# Recover the central size-two order-three MN3B class.
mn3bOrders := OrdersClassRepresentatives(mn3b);
mn3bSizes := SizesConjugacyClasses(mn3b);
centralCandidates := Filtered([1..Length(mn3bOrders)], i ->
  mn3bOrders[i] = 3 and mn3bSizes[i] = 2);
if Length(centralCandidates) <> 1 then
  Error("expected a unique size-two order-three MN3B central class");
fi;
central3B := centralCandidates[1];

# In the centralizer, the two nonidentity centre elements should be distinct
# singleton conjugacy classes, both fusing to the single MN3B size-two class.
inertiaOrders := OrdersClassRepresentatives(inertia);
inertiaSizes := SizesConjugacyClasses(inertia);
centralLiftClasses := Filtered([1..Length(fusion)], i ->
  fusion[i] = central3B and inertiaOrders[i] = 3 and inertiaSizes[i] = 1);
if Length(centralLiftClasses) <> 2 then
  Error("expected two singleton inertia classes above the fused MN3B central class");
fi;
chosenZClass := centralLiftClasses[1];
chosenZInverseClass := centralLiftClasses[2];

# Reconstruct the 196883 restriction and its MN3B irreducible decomposition.
monster := CharacterTable("M");
if monster = fail then Error("Monster character table is unavailable"); fi;
monsterIrr := Irr(monster);
chiPositions := Filtered([1..Length(monsterIrr)], i -> monsterIrr[i][1] = 196883);
if Length(chiPositions) <> 1 then Error("expected one degree-196883 Monster irreducible"); fi;
monsterFusion := GetFusionMap(mn3b, monster);
if monsterFusion = fail then Error("MN3B -> Monster fusion unavailable"); fi;
restricted := ClassFunction(mn3b, List(monsterFusion, i -> monsterIrr[chiPositions[1]][i]));
mn3bIrr := Irr(mn3b);
mults := List(mn3bIrr, psi -> ScalarProduct(mn3b, restricted, psi));
nonzero := Filtered([1..Length(mults)], i -> mults[i] <> 0);

# Re-identify the paired-phase MN3B constituents by the exact central trace
# ratio chi(z)=-degree/2.
paired := Filtered(nonzero, i ->
  2 * mn3bIrr[i][central3B] = -mn3bIrr[i][1]);
if Length(paired) = 0 then Error("no paired-phase MN3B constituents found"); fi;

inertiaIrr := Irr(inertia);
zeta := E(3);
zeta2 := E(3)^2;
records := [];
phaseMultiplicityDegrees := [];

for i in paired do
  psi := mn3bIrr[i];
  psiRes := ClassFunction(inertia, List(fusion, c -> psi[c]));
  coeffs := List(inertiaIrr, theta -> ScalarProduct(inertia, psiRes, theta));
  support := Filtered([1..Length(coeffs)], j -> coeffs[j] <> 0);
  if ForAny(support, j -> not IsInt(coeffs[j]) or coeffs[j] < 0) then
    Error("paired constituent restriction has nonintegral/negative inertia multiplicity");
  fi;

  zetaSupport := [];
  zeta2Support := [];
  for j in support do
    degree := inertiaIrr[j][1];
    centralValue := inertiaIrr[j][chosenZClass];
    if centralValue = degree * zeta then
      Add(zetaSupport, j);
    elif centralValue = degree * zeta2 then
      Add(zeta2Support, j);
    else
      Error("inertia constituent is not pure zeta or zeta^2 on chosen central class");
    fi;
  od;

  zetaDegree := Sum(zetaSupport, j -> coeffs[j] * inertiaIrr[j][1]);
  zeta2Degree := Sum(zeta2Support, j -> coeffs[j] * inertiaIrr[j][1]);
  if zetaDegree <> zeta2Degree then
    Error("paired MN3B constituent does not split into equal zeta/zeta^2 degrees");
  fi;
  if zetaDegree + zeta2Degree <> psi[1] then
    Error("phase-resolved inertia degrees do not reconstruct MN3B constituent degree");
  fi;
  if zetaDegree mod 729 <> 0 then
    Error("phase-resolved zeta degree is not divisible by 729");
  fi;
  multiplicityDegree := zetaDegree / 729;
  Add(phaseMultiplicityDegrees, multiplicityDegree);
  Add(records, rec(
    mn3bPosition := i,
    mn3bDegree := psi[1],
    mn3bMultiplicity := mults[i],
    zetaDegree := zetaDegree,
    zetaSquaredDegree := zeta2Degree,
    multiplicityDegree := multiplicityDegree,
    zetaSupport := zetaSupport,
    zetaSquaredSupport := zeta2Support
  ));
od;

Sort(phaseMultiplicityDegrees);
if phaseMultiplicityDegrees <> [12, 78] then
  Error("phase-resolved multiplicity degrees are not exactly 12 and 78");
fi;

output := OutputTextFile("build/monster_3b_inertia_phase_resolution.json", false);
SetPrintFormattingStatus(output, false);
PrintTo(output,
  "{\n",
  "  \"mn3b_table\": \"", Identifier(mn3b), "\",\n",
  "  \"inertia_table\": \"", Identifier(inertia), "\",\n",
  "  \"inertia_requested_name\": \"", inertiaName, "\",\n",
  "  \"mn3b_central_class_position\": ", central3B, ",\n",
  "  \"chosen_zeta_central_class_position\": ", chosenZClass, ",\n",
  "  \"chosen_zeta_squared_central_class_position\": ", chosenZInverseClass, ",\n",
  "  \"phase_resolved_multiplicity_degrees\": [12, 78],\n",
  "  \"phase_resolution_certified\": true,\n",
  "  \"records\": [\n");
for k in [1..Length(records)] do
  r := records[k];
  PrintTo(output,
    "    {\"mn3b_position\": ", r.mn3bPosition,
    ", \"mn3b_degree\": ", r.mn3bDegree,
    ", \"mn3b_multiplicity\": ", r.mn3bMultiplicity,
    ", \"zeta_degree\": ", r.zetaDegree,
    ", \"zeta_squared_degree\": ", r.zetaSquaredDegree,
    ", \"multiplicity_degree\": ", r.multiplicityDegree, "}"
  );
  if k < Length(records) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ]\n}\n");
CloseStream(output);

Print("3B inertia phase-resolution certificate written; multiplicities [12,78].\n");
QUIT;
