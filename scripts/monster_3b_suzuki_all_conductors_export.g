# Minimal source export for independent no-GAP exact character comparison.
# This is a ONE-TIME optional producer, NOT a claimed local GAP run.
# Requires CTblLib; output is consumed by:
# scripts/monster_3b_suzuki_all_conductors_character_audit.py.
#
# Original 6.Suz character values/power map: CTblLib / ATLAS sources.
# Original Monster normalizer construction: Barraclough--Wilson (2007).
# Exact cyclotomic coefficient extractor: GAP Reference Manual,
# Chapter 18.1-10 "CoeffsCyc".
# Gabriele Nebe (2025) establishes irreducible Sym²(12) degree78
# (nonfaithful to 6.Suz); that does NOT identify Monster occurrence.
#
# General-conductor EXACT export: 6.Suz rows need not lie in Q(zeta3).
# Original Q(zeta3) fast-path exporter remains available.
#
# Run from the repository root:
#   mkdir -p build
#   gap -q scripts/monster_3b_suzuki_all_conductors_export.g
#   python scripts/monster_3b_suzuki_all_conductors_character_audit.py
#     build/monster_3b_suzuki_all_conductors_characters.json

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

# Each exact source value has its own conductor, so never truncate
# 6.Suz characters to Q(zeta3) before source comparison.
# GAP CoeffsCyc(x,n) is an exact Zumbroich-basis expansion at n.
FullCyclotomicRecord := function(x)
  local n, coeff, reconstructed;
  n := Conductor(x);
  if not IsInt(n) or n < 1 or n > 4096 then
    Error("source conductor exceeds backend-free exact limit");
  fi;
  coeff := CoeffsCyc(x,n);
  if coeff = fail or Length(coeff) <> n then
    Error("source exact cyclotomic row unavailable");
  fi;
  reconstructed := Sum([1..n], j -> coeff[j]*E(n)^(j-1));
  if reconstructed <> x then
    Error("original coefficient row reconstruction failed");
  fi;
  return rec(conductor:=n,coefficients:=List(coeff,String));
end;

out := OutputTextFile(
  "build/monster_3b_suzuki_all_conductors_characters.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"table_id\":\"6.Suz\",\n");
AppendTo(out,"  \"gap_runtime_version\":\"",GAPInfo.Version,"\",\n");
AppendTo(out,"  \"ctbllib_runtime_version\":\"",GAPInfo.PackagesLoaded.ctbllib[2],"\",\n");
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
  local k, j, idx, x, ab, t;
  AppendTo(out,"[\n");
  for k in [1..Length(indices)] do
    idx := indices[k];
    AppendTo(out,"    {\"label\":",Monster3BSourceJSONQuotedLabel(labels[idx]),
      ",\"source_irreducible_position_1_based\":",String(idx),
      ",\"values\":[");
    for j in [1..Length(classOrders)] do
      x := irr[idx][j];
      ab := FullCyclotomicRecord(x);
      AppendTo(out,"{\"conductor\":",String(ab.conductor),
        ",\"coefficients\":[");
      for t in [1..Length(ab.coefficients)] do
        AppendTo(out,"\"",ab.coefficients[t],"\"");
        if t < Length(ab.coefficients) then AppendTo(out,","); fi;
      od;
      AppendTo(out,"]}");
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
Print("6.Suz all-conductor exact degree12/all78 export written.\n");
Print("No Monster selected family or source execution provenance claimed.\n");
QUIT;
