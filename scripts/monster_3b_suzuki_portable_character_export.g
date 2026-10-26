# Minimal source export for independent no-GAP exact character comparison.
# This is a ONE-TIME optional producer, NOT a claimed local GAP run.
# Requires CTblLib; output is consumed by:
# scripts/monster_3b_suzuki_portable_character_checker.py.
#
# Original 6.Suz character values/power map: CTblLib / ATLAS sources.
# Original Monster normalizer construction: Barraclough--Wilson (2007).
# Exact cyclotomic coefficient extractor: GAP Reference Manual,
# Chapter 18.1-10 "CoeffsCyc".
# Gabriele Nebe (2025) establishes irreducible Sym²(12) degree78
# (nonfaithful to 6.Suz); that does NOT identify Monster occurrence.
#
# Fail-closed field restriction: the portable checker is for Q(zeta3).
# If any required full-class character value is NOT in Q(zeta3), ERROR
# rather than silently approximate or drop a class. An arbitrary-degree
# cyclotomic field would require a DIFFERENT explicitly typed checker.
#
# Run from the repository root:
#   mkdir -p build
#   gap -q scripts/monster_3b_suzuki_portable_character_export.g
#   python scripts/monster_3b_suzuki_portable_character_checker.py
#     build/monster_3b_suzuki_portable_source_characters.json

if LoadPackage("ctbllib") <> true then Error("CTblLib required"); fi;
Read("scripts/monster_3b_source_json_escape.g");
six := CharacterTable("6.Suz");
if six = fail then Error("6.Suz source ordinary table unavailable"); fi;
irr := Irr(six);
labels := AtlasLabelsOfIrreducibles(six, "short");
if labels = fail or Length(labels) <> Length(irr) then
  Error("6.Suz ATLAS labels missing");
fi;
classOrders := OrdersClassRepresentatives(six);
classSizes := SizesConjugacyClasses(six);
groupOrder := Size(six);
if Sum(classSizes) <> groupOrder or classSizes[1] <> 1 then
  Error("source group order/class sizes mismatch");
fi;
pow2 := PowerMap(six,2);
if pow2 = fail or Length(pow2) <> Length(classOrders) then
  Error("actual class second power map required");
fi;
cent := ClassPositionsOfCentre(six);
c2 := Filtered(cent, i -> classOrders[i] = 2);
c3 := Filtered(cent, i -> classOrders[i] = 3);
if Length(c2) <> 1 or Length(c3) <> 2 then
  Error("source 6.Suz centre must have one C2 and two C3 classes");
fi;

IsFaithfulCharacter := chi -> ClassPositionsOfKernel(chi) = [1];
p12 := Filtered([1..Length(irr)], i ->
  irr[i][1] = 12 and IsFaithfulCharacter(irr[i]));
p78 := Filtered([1..Length(irr)], i -> irr[i][1] = 78);
if Length(p12) <> 2 or Length(p78) < 2 then
  Error("degree12 source pair / all degree78 rows missing");
fi;

# GAP CoeffsCyc(x,3) expresses x as a linear combination of
# {1,zeta,zeta²}. Reduce zeta²=-1-zeta to Q-basis (1,zeta).
# This is safe independent of GAP's choice of Zumbroich basis.
QZeta3Pair := function(x)
  local coeff, a, b;
  coeff := CoeffsCyc(x,3);
  if coeff = fail or Length(coeff) <> 3 then
    Error("source character contains field value outside Q(zeta3)");
  fi;
  a := coeff[1] - coeff[3];
  b := coeff[2] - coeff[3];
  if x <> a + b*E(3) then
    Error("non-exact 1,zeta coordinate reconstruction");
  fi;
  return [String(a),String(b)];
end;

out := OutputTextFile(
  "build/monster_3b_suzuki_portable_source_characters.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"table_id\":\"6.Suz\",\n");
AppendTo(out,"  \"group_order\":",String(groupOrder),",\n");
AppendTo(out,"  \"class_sizes\":[");
for k in [1..Length(classSizes)] do
  AppendTo(out,String(classSizes[k]));
  if k < Length(classSizes) then AppendTo(out,","); fi;
od;
AppendTo(out,"],\n  \"class_orders\":[");
for k in [1..Length(classOrders)] do
  AppendTo(out,String(classOrders[k]));
  if k < Length(classOrders) then AppendTo(out,","); fi;
od;
AppendTo(out,"],\n  \"power_map_2_zero_based\":[");
for k in [1..Length(pow2)] do
  AppendTo(out,String(pow2[k]-1));
  if k < Length(pow2) then AppendTo(out,","); fi;
od;
AppendTo(out,"],\n  \"central_c2_zero_based\":",
  String(c2[1]-1),",\n");
AppendTo(out,"  \"central_c3_zero_based\":",
  String(c3[1]-1),",\n");

WriteRowArray := function(indices)
  local k, j, idx, x, ab;
  AppendTo(out,"[\n");
  for k in [1..Length(indices)] do
    idx := indices[k];
    AppendTo(out,"    {\"label\":",Monster3BSourceJSONQuotedLabel(labels[idx]),
      ",\"source_irreducible_position_1_based\":",String(idx),
      ",\"values\":[");
    for j in [1..Length(classOrders)] do
      x := irr[idx][j];
      ab := QZeta3Pair(x);
      AppendTo(out,"[\"",ab[1],"\",\"",ab[2],"\"]");
      if j < Length(classOrders) then AppendTo(out,","); fi;
    od;
    AppendTo(out,"]}");
    if k < Length(indices) then AppendTo(out,","); fi;
    AppendTo(out,"\n");
  od;
  AppendTo(out,"  ]");
end;

AppendTo(out,"  \"degree12\":");
WriteRowArray(p12);
AppendTo(out,",\n  \"degree78\":");
WriteRowArray(p78);
AppendTo(out,"\n}\n");
CloseStream(out);
Print("6.Suz exact Q(zeta3) degree12/all78 full-character export written.\n");
Print("No Monster selected family or source execution provenance claimed.\n");
QUIT;
