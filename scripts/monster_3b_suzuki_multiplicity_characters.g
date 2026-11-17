# Identify the source-native 6.Suz multiplicity characters behind the
# Barraclough--Wilson degree-729 inertia construction.
#
# PRIMARY SOURCE
# R. W. Barraclough; R. A. Wilson,
# "The Character Table of a Maximal Subgroup of the Monster",
# LMS J. Comput. Math. 10 (2007), 161--175.
# DOI: 10.1112/S1461157000001352.
#
# Section 5.1 states that the two degree-729 irreducible characters of the
# extraspecial 3^(1+12) extend to 3^(1+12):6.Suz, and that every eta-hat in
# Irr(6.Suz) inflates to the inertia group before tensoring with the 729
# extension and inducing to the outer group.
#
# COMPUTATIONAL SOURCE / IDENTIFIER LAYER
# Thomas Breuer and CTblLib contributors, GAP Character Table Library.
# `AtlasLabelsOfIrreducibles` supplies stable ATLAS-style semantic labels for
# the same ordered list returned by Irr(tbl).  The numeric position remains an
# execution coordinate; the label is an external character identity coordinate.
# Neither one by itself proves occurrence in the Monster restriction.
#
# This producer pins faithful 12/78 as used by the historical Monster
# quotient matcher, while separately inventorying nonfaithful degree78.
# Nebe's Sym²(faithful12) is nonfaithful, not a replacement for faithful78.  It does NOT infer
# that every candidate occurs in the Monster restriction; that same-object
# match remains a separate payment.

if LoadPackage("ctbllib") <> true then
  Error("CTblLib is required");
fi;

tbl := CharacterTable("6.Suz");
outer := CharacterTable("6.Suz.2");
if tbl = fail or outer = fail then
  Error("6.Suz / 6.Suz.2 character tables are unavailable");
fi;

irr := Irr(tbl);
labels := AtlasLabelsOfIrreducibles(tbl, "short");
if labels = fail or Length(labels) <> Length(irr) then
  Error("ATLAS irreducible labels for 6.Suz are unavailable or misaligned");
fi;

centre := ClassPositionsOfCentre(tbl);
orders := OrdersClassRepresentatives(tbl);
central3 := Filtered(centre, i -> orders[i] = 3);
if Length(central3) <> 2 then
  Error("expected two nonidentity central order-three classes in 6.Suz");
fi;

IsFaithfulCharacter := function(chi)
  return ClassPositionsOfKernel(chi) = [1];
end;

faithful12 := Filtered([1..Length(irr)], i ->
  irr[i][1] = 12 and IsFaithfulCharacter(irr[i]));
# Faithful degree78 is the SAME family used by the source-to-Monster
# quotient matcher; nonfaithful degree78 (including Sym²(12)) is distinct.
faithful78 := Filtered([1..Length(irr)], i ->
  irr[i][1] = 78 and IsFaithfulCharacter(irr[i]));
allDegree78 := Filtered([1..Length(irr)], i -> irr[i][1] = 78);
nonfaithful78 := Filtered(allDegree78, i ->
  not IsFaithfulCharacter(irr[i]));
if Length(faithful12) <> 2 or Length(allDegree78) < 2 then
  Error("need faithful twelve pair and complete degree78 inventory");
fi;

fusion := FusionConjugacyClasses(tbl, outer);
if fusion = fail then
  Error("stored/computable 6.Suz -> 6.Suz.2 class fusion is unavailable");
fi;

zeta := E(3);
zeta2 := E(3)^2;

PhaseLabel := function(chi, cls)
  local degree, value;
  degree := chi[1];
  value := chi[cls];
  if value = degree then
    return "trivial";
  elif value = degree * zeta then
    return "zeta";
  elif value = degree * zeta2 then
    return "zetaSquared";
  else
    return "other";
  fi;
end;

RowsFor := function(positions)
  local rows, p, chi;
  rows := [];
  for p in positions do
    chi := irr[p];
    Add(rows, rec(
      position := p,
      faithfulToSixSuz := IsFaithfulCharacter(chi),
      atlasLabel := labels[p],
      degree := chi[1],
      firstCentralValue := chi[central3[1]],
      secondCentralValue := chi[central3[2]],
      firstCentralPhase := PhaseLabel(chi, central3[1]),
      secondCentralPhase := PhaseLabel(chi, central3[2])
    ));
  od;
  return rows;
end;

rows12 := RowsFor(faithful12);
rows78 := RowsFor(allDegree78);

# Source character central-C3 scalar may be TRIVIAL on nonfaithful
# degree78 characters; do NOT omit them before Monster quotient matching.
for row in Concatenation(rows12, rows78) do
  if row.firstCentralPhase = "other" or row.secondCentralPhase = "other" then
    Error("central C3 character is not a pure order-three scalar");
  fi;
  if row.firstCentralPhase = "trivial" then
    if row.secondCentralPhase <> "trivial" then
      Error("trivial first central scalar has nontrivial second scalar");
    fi;
  elif row.firstCentralPhase = row.secondCentralPhase then
    Error("nontrivial central C3 class scalars must be inverse phases");
  fi;
od;
if ForAny(rows12, r -> r.firstCentralPhase = "trivial") then
  Error("faithful degree12 must not have trivial central C3 scalar");
fi;
if rows12[1].atlasLabel = rows12[2].atlasLabel then
  Error("faithful 12 ATLAS labels not distinct");
fi;
if Length(Set(List(rows78,r -> r.atlasLabel))) <> Length(rows78) then
  Error("degree78 atlas labels not unique");
fi;

# Strict JSON row output, with no assumptions about the number of 78s.
JoinIntPositions := xs -> JoinStringsWithSeparator(List(xs,String),",");
JoinAtlasLabels := xs ->
  JoinStringsWithSeparator(List(xs,
    i -> Concatenation("\"",labels[i],"\"")),",");

output := OutputTextFile("build/monster_3b_suzuki_multiplicity_characters.json", false);
SetPrintFormattingStatus(output, false);
PrintTo(output,
  "{\n",
  "  \"table\": \"6.Suz\",\n",
  "  \"outer_table\": \"6.Suz.2\",\n",
  "  \"label_source\": \"CTblLib AtlasLabelsOfIrreducibles(short)\",\n",
  "  \"central_order_three_classes\": [", central3[1], ", ", central3[2], "],\n",
  "  \"faithful_degree_12_positions\": ", faithful12, ",\n",
  "  \"degree_78_positions\": [", JoinIntPositions(allDegree78), "],\n",
  "  \"degree_78_family_filter\": \"all_character_degrees_no_faithfulness_filter\",\n",
  "  \"all_degree_78_positions\": [", JoinIntPositions(allDegree78), "],\n",
  "  \"nonfaithful_degree_78_positions\": [", JoinIntPositions(nonfaithful78), "],\n",
  "  \"faithful_degree_78_positions\": [", JoinIntPositions(faithful78), "],\n",
  "  \"faithful_degree_12_atlas_labels\": [\"", rows12[1].atlasLabel, "\", \"", rows12[2].atlasLabel, "\"],\n",
  "  \"degree_78_atlas_labels\": [", JoinAtlasLabels(allDegree78), "],\n",
  "  \"fusion_length\": ", Length(fusion), ",\n",
  "  \"source_native_729_tensor_factorisation\": true,\n",
  "  \"atlas_label_position_alignment_paid\": true,\n",
  "  \"monster_same_object_match_paid\": false,\n",
  "  \"degree_12_rows\": [\n");
for k in [1..Length(rows12)] do
  r := rows12[k];
  PrintTo(output,
    "    {\"position\": ", r.position,
    ", \"atlas_label\": \"", r.atlasLabel, "\"",
    ", \"degree\": 12",
    ", \"faithful_to_6Suz\": ", r.faithfulToSixSuz,
    ", \"first_central_phase\": \"", r.firstCentralPhase, "\"",
    ", \"second_central_phase\": \"", r.secondCentralPhase, "\"}"
  );
  if k < Length(rows12) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ],\n  \"degree_78_rows\": [\n");
for k in [1..Length(rows78)] do
  r := rows78[k];
  PrintTo(output,
    "    {\"position\": ", r.position,
    ", \"atlas_label\": \"", r.atlasLabel, "\"",
    ", \"degree\": 78",
    ", \"faithful_to_6Suz\": ", r.faithfulToSixSuz,
    ", \"first_central_phase\": \"", r.firstCentralPhase, "\"",
    ", \"second_central_phase\": \"", r.secondCentralPhase, "\"}"
  );
  if k < Length(rows78) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ]\n}\n");
CloseStream(output);

Print("6.Suz faithful12 and ALL degree78 candidate receipt written with kernels.\n");
QUIT;
