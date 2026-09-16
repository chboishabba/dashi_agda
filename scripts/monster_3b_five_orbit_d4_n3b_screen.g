# Screen the actual restricted Monster character on MN3B against the
# five-orbit D4 target character
#
#   theta = (5,5,1,3,3) = 3 A1 + B1 + B2.
#
# Stage 1 is purely character-theoretic: enumerate every admissible D8 -> MN3B
# class fusion and retain those for which the actual degree-196883 Monster
# character restricted along the fusion contains theta as a subcharacter.
#
# Stage 2 tries to realize an actual D8 subgroup inside the constructible MN3B
# model already used by monster_3b_actual_kernel_structure.g. A concrete
# subgroup is promoted only after an explicit isomorphism from the canonical D4
# has transported the canonical class representatives into that subgroup, and
# every transported representative maps uniquely to an MN3B table class by the
# pair (element order, ambient conjugacy-class size).
#
# The runtime receipt is deliberately fail-locating: AtlasRep/CTblLib group
# realization, subgroup discovery, canonical isomorphism, unique ambient class
# fusion, admissibility of the realized fusion and character compatibility are
# retained as separate booleans. No character match creates the
# Selected3BNormalizerMonsterActionWeld or an intertwiner on the selected
# Monster carrier.

if LoadPackage("ctbllib") <> true then
  Error("CTblLib is required");
fi;
if LoadPackage("atlasrep") <> true then
  Error("AtlasRep is required");
fi;

monster := CharacterTable("M");
mn3b := CharacterTable("MN3B");
if monster = fail or mn3b = fail then
  Error("required character tables M and MN3B are unavailable");
fi;

# ----------------------------------------------------------------------
# Canonical abstract D4 and the five-orbit quotient action.
# ----------------------------------------------------------------------

r := (1,2,3,4);
s := (2,4);
d4Group := Group([r,s]);
if Size(d4Group) <> 8 or not IsAbelian(d4Group) then
  Error("failed to construct the canonical order-eight dihedral group");
fi;
d4 := CharacterTable(d4Group);
d4Classes := ConjugacyClasses(d4Group);
d4Irr := Irr(d4);

permR := (2,3)(4,5);
permS := (4,5);
quotientAction := GroupHomomorphismByImages(
  d4Group, Group([permR,permS]), [r,s], [permR,permS]);
if quotientAction = fail then
  Error("failed to construct the five-orbit quotient action");
fi;

targetValues := List(d4Classes, cl ->
  Number([1..5], i -> i ^ Image(quotientAction, Representative(cl)) = i));
target := ClassFunction(d4, targetValues);
targetMult := List(d4Irr, psi -> ScalarProduct(d4, target, psi));

classE := PositionProperty(d4Classes, cl -> One(d4Group) in Elements(cl));
classR2 := PositionProperty(d4Classes, cl -> r^2 in Elements(cl));
classR := PositionProperty(d4Classes, cl -> r in Elements(cl));
classAxis := PositionProperty(d4Classes, cl -> s in Elements(cl));
classDiag := PositionProperty(d4Classes, cl -> r*s in Elements(cl));
if fail in [classE,classR2,classR,classAxis,classDiag] then
  Error("failed to identify canonical D4 classes");
fi;
canonicalClassOrder := [classE,classR2,classR,classAxis,classDiag];
canonicalTargetValues := List(canonicalClassOrder, i -> targetValues[i]);
if canonicalTargetValues <> [5,5,1,3,3] then
  Error("five-orbit D4 action does not reproduce target character (5,5,1,3,3)");
fi;

FindIrrByCanonicalValues := function(values)
  local positions;
  positions := Filtered([1..Length(d4Irr)], i ->
    List(canonicalClassOrder, c -> d4Irr[i][c]) = values);
  if Length(positions) <> 1 then
    Error("D4 irreducible character label is not unique");
  fi;
  return positions[1];
end;

posA1 := FindIrrByCanonicalValues([1,1,1,1,1]);
posA2 := FindIrrByCanonicalValues([1,1,1,-1,-1]);
posB1 := FindIrrByCanonicalValues([1,1,-1,1,-1]);
posB2 := FindIrrByCanonicalValues([1,1,-1,-1,1]);
posE  := FindIrrByCanonicalValues([2,-2,0,0,0]);

if [targetMult[posA1],targetMult[posA2],targetMult[posB1],targetMult[posB2],targetMult[posE]]
   <> [3,0,1,1,0] then
  Error("target D4 multiplicities are not 3A1+B1+B2");
fi;

monsterIrr := Irr(monster);
chiPositions := Filtered([1..Length(monsterIrr)], i -> monsterIrr[i][1] = 196883);
if Length(chiPositions) <> 1 then
  Error("expected exactly one Monster irreducible of degree 196883");
fi;
chiMonster := monsterIrr[chiPositions[1]];
mn3bToMonster := GetFusionMap(mn3b, monster);
if mn3bToMonster = fail then
  Error("stored MN3B -> Monster class fusion is unavailable");
fi;
chiMN3BValues := List(mn3bToMonster, i -> chiMonster[i]);

possibleFusions := PossibleClassFusions(d4, mn3b);
if possibleFusions = fail then
  possibleFusions := [];
fi;

compatible := [];
for fusion in possibleFusions do
  pulledValues := List(fusion, i -> chiMN3BValues[i]);
  pulled := ClassFunction(d4, pulledValues);
  multiplicities := List(d4Irr, psi -> ScalarProduct(d4, pulled, psi));
  if ForAll([1..Length(d4Irr)], i -> IsInt(multiplicities[i]) and multiplicities[i] >= targetMult[i]) then
    Add(compatible, rec(
      fusion := fusion,
      multiplicities := multiplicities,
      canonicalValues := List(canonicalClassOrder, c -> pulledValues[c])
    ));
  fi;
od;

expectedGroupOrder := Size(mn3b);
groupNames := ["MN3B","3^(1+12).2.Suz.2","3^(1+12):2.Suz.2","3^1+12.2.Suz.2"];
G := fail;
atlasGroupRealized := false;
selectedConstructionSource := fail;

for groupName in groupNames do
  infos := AllAtlasGeneratingSetInfos(groupName);
  infos := Filtered(infos, info -> IsBound(info.size) and info.size = expectedGroupOrder);
  for info in infos do
    candidate := AtlasGroup(info);
    if candidate <> fail and Size(candidate) = expectedGroupOrder then
      G := candidate;
      atlasGroupRealized := true;
      selectedConstructionSource := "AtlasRep-info";
      break;
    fi;
  od;
  if G <> fail then break; fi;
od;

if G = fail then
  for groupName in groupNames do
    candidate := AtlasGroup(groupName);
    if candidate <> fail and Size(candidate) = expectedGroupOrder then
      G := candidate;
      atlasGroupRealized := true;
      selectedConstructionSource := "AtlasGroup-direct";
      break;
    fi;
  od;
fi;

if G = fail and LoadPackage("browse") = true then
  groupInfos := GroupInfoForCharacterTable(mn3b);
  for groupInfo in groupInfos do
    candidate := GroupForGroupInfo(groupInfo);
    if candidate <> fail and Size(candidate) = expectedGroupOrder then
      G := candidate;
      atlasGroupRealized := true;
      selectedConstructionSource := "CTblLib-GroupForGroupInfo";
      break;
    fi;
  od;
fi;

actualD4 := fail;
actualFusion := fail;
actualCompatible := false;
d4SubgroupFound := false;
canonicalIsomorphismFound := false;
ambientClassFusionUnique := false;
actualFusionIsPossible := false;

if G <> fail then
  P := SylowSubgroup(G,2);
  pElements := Elements(P);
  order4Elements := Filtered(pElements, x -> Order(x) = 4);

  for rr in order4Elements do
    C4 := Group([rr]);
    N := Normalizer(P,C4);
    candidatesS := Filtered(Elements(N), x ->
      Order(x) = 2 and not x in C4 and rr^x = rr^-1);
    if Length(candidatesS) > 0 then
      H := Group([rr,candidatesS[1]]);
      if Size(H) = 8 and not IsAbelian(H) then
        actualD4 := H;
        d4SubgroupFound := true;
        break;
      fi;
    fi;
  od;

  if actualD4 <> fail then
    canonicalToActual := IsomorphismGroups(d4Group,actualD4);
    if canonicalToActual <> fail then
      canonicalIsomorphismFound := true;
      mnOrders := OrdersClassRepresentatives(mn3b);
      mnSizes := SizesConjugacyClasses(mn3b);
      candidateFusion := List([1..Length(d4Classes)], i -> fail);
      unique := true;
      for canonicalPosition in [1..Length(d4Classes)] do
        x := Image(canonicalToActual,Representative(d4Classes[canonicalPosition]));
        xOrder := Order(x);
        ambientCentralizerSize := Size(Centralizer(G,x));
        ambientClassSize := Size(G) / ambientCentralizerSize;
        matches := Filtered([1..Length(mnOrders)], i ->
          mnOrders[i] = xOrder and mnSizes[i] = ambientClassSize);
        if Length(matches) <> 1 then
          unique := false;
          break;
        fi;
        candidateFusion[canonicalPosition] := matches[1];
      od;
      if unique then
        ambientClassFusionUnique := true;
        actualFusion := candidateFusion;
        if actualFusion in possibleFusions then
          actualFusionIsPossible := true;
          compatibleFusions := List(compatible, item -> item.fusion);
          actualCompatible := actualFusion in compatibleFusions;
        fi;
      fi;
    fi;
  fi;
fi;

actualD4SubgroupRealized := d4SubgroupFound and canonicalIsomorphismFound and ambientClassFusionUnique;

JsonBool := function(x)
  if x then return "true"; else return "false"; fi;
end;

PrintIntList := function(out, xs)
  local i;
  AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i > 1 then AppendTo(out,","); fi;
    AppendTo(out,String(xs[i]));
  od;
  AppendTo(out,"]");
end;

output := OutputTextFile("build/monster_3b_five_orbit_d4_n3b_screen.json", false);
SetPrintFormattingStatus(output,false);
AppendTo(output,"{\n");
AppendTo(output,"  \"target_character\": [5,5,1,3,3],\n");
AppendTo(output,"  \"target_multiplicities\": {\"A1\":3,\"A2\":0,\"B1\":1,\"B2\":1,\"E\":0},\n");
AppendTo(output,"  \"possible_fusion_count\": ",String(Length(possibleFusions)),",\n");
AppendTo(output,"  \"character_compatible_fusion_count\": ",String(Length(compatible)),",\n");
AppendTo(output,"  \"atlas_group_realized\": ",JsonBool(atlasGroupRealized),",\n");
if selectedConstructionSource = fail then
  AppendTo(output,"  \"group_construction_source\": null,\n");
else
  AppendTo(output,"  \"group_construction_source\": \"",selectedConstructionSource,"\",\n");
fi;
AppendTo(output,"  \"d4_subgroup_found\": ",JsonBool(d4SubgroupFound),",\n");
AppendTo(output,"  \"canonical_isomorphism_found\": ",JsonBool(canonicalIsomorphismFound),",\n");
AppendTo(output,"  \"ambient_class_fusion_unique\": ",JsonBool(ambientClassFusionUnique),",\n");
AppendTo(output,"  \"actual_fusion_is_possible\": ",JsonBool(actualFusionIsPossible),",\n");
AppendTo(output,"  \"actual_d4_subgroup_realized\": ",JsonBool(actualD4SubgroupRealized),",\n");
AppendTo(output,"  \"actual_character_compatible\": ",JsonBool(actualCompatible),",\n");
if actualFusion = fail then
  AppendTo(output,"  \"actual_realized_fusion\": null,\n");
else
  AppendTo(output,"  \"actual_realized_fusion\": ");
  PrintIntList(output,actualFusion);
  AppendTo(output,",\n");
fi;
AppendTo(output,"  \"possible_fusion_is_actual_subgroup\": false,\n");
AppendTo(output,"  \"character_match_creates_intertwiner\": false,\n");
AppendTo(output,"  \"selected_action_same_object_paid\": false\n");
AppendTo(output,"}\n");
CloseStream(output);

Print("D4/N3B character screen written: possible=",Length(possibleFusions),
  "; compatible=",Length(compatible),
  "; group-source=",selectedConstructionSource,
  "; atlas-group=",atlasGroupRealized,
  "; d4-found=",d4SubgroupFound,
  "; canonical-iso=",canonicalIsomorphismFound,
  "; fusion-unique=",ambientClassFusionUnique,
  "; fusion-possible=",actualFusionIsPossible,
  "; actual-compatible=",actualCompatible,"\n");
QUIT;
