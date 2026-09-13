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
# This producer identifies the faithful degree-12 and degree-78 6.Suz
# candidates and records their central order-three phases.  It does NOT infer
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
faithful78 := Filtered([1..Length(irr)], i ->
  irr[i][1] = 78 and IsFaithfulCharacter(irr[i]));

# CTblLib's published 6.Suz examples use the ATLAS families 12ab and 78ab.
# Fail closed if a future table version changes that exact candidate count.
if Length(faithful12) <> 2 then
  Error("expected exactly two faithful degree-12 irreducibles in 6.Suz");
fi;
if Length(faithful78) <> 2 then
  Error("expected exactly two faithful degree-78 irreducibles in 6.Suz");
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
  if value = degree * zeta then
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
rows78 := RowsFor(faithful78);

# Every faithful candidate must carry a pure nontrivial C3 scalar on each
# central order-three class, with the two classes giving inverse phases.
for row in Concatenation(rows12, rows78) do
  if not (row.firstCentralPhase in ["zeta", "zetaSquared"]) then
    Error("faithful Suzuki candidate is not pure zeta/zeta^2 on first central C3 class");
  fi;
  if not (row.secondCentralPhase in ["zeta", "zetaSquared"]) then
    Error("faithful Suzuki candidate is not pure zeta/zeta^2 on second central C3 class");
  fi;
  if row.firstCentralPhase = row.secondCentralPhase then
    Error("two nonidentity central C3 classes did not produce inverse phases");
  fi;
od;

# The two candidates in each degree must be separately labelled; this catches
# accidental table-order/label collapse without guessing which member occurs in
# the Monster restriction.
if rows12[1].atlasLabel = rows12[2].atlasLabel then
  Error("faithful degree-12 candidates have duplicate ATLAS labels");
fi;
if rows78[1].atlasLabel = rows78[2].atlasLabel then
  Error("faithful degree-78 candidates have duplicate ATLAS labels");
fi;

output := OutputTextFile("build/monster_3b_suzuki_multiplicity_characters.json", false);
SetPrintFormattingStatus(output, false);
PrintTo(output,
  "{\n",
  "  \"table\": \"6.Suz\",\n",
  "  \"outer_table\": \"6.Suz.2\",\n",
  "  \"label_source\": \"CTblLib AtlasLabelsOfIrreducibles(short)\",\n",
  "  \"central_order_three_classes\": [", central3[1], ", ", central3[2], "],\n",
  "  \"faithful_degree_12_positions\": ", faithful12, ",\n",
  "  \"faithful_degree_78_positions\": ", faithful78, ",\n",
  "  \"faithful_degree_12_atlas_labels\": [\"", rows12[1].atlasLabel, "\", \"", rows12[2].atlasLabel, "\"],\n",
  "  \"faithful_degree_78_atlas_labels\": [\"", rows78[1].atlasLabel, "\", \"", rows78[2].atlasLabel, "\"],\n",
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
    ", \"first_central_phase\": \"", r.firstCentralPhase, "\"",
    ", \"second_central_phase\": \"", r.secondCentralPhase, "\"}"
  );
  if k < Length(rows78) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;
PrintTo(output, "  ]\n}\n");
CloseStream(output);

Print("6.Suz faithful 12/78 multiplicity-character candidate receipt written with ATLAS labels.\n");
QUIT;
