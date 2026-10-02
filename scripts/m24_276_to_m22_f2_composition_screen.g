# Restrict the actual ATLAS M24 permutation action on 276 points to the
# point stabilizer M22:2 and its derived subgroup M22, then compute the
# characteristic-two composition factors of the full 276-dimensional
# permutation module.
#
# This is a finite candidate for the 2B 276 -> Completion10 weld because:
#   * the source action has exactly 276 points;
#   * the point stabilizer is M22:2 (ATLAS metadata);
#   * M22 is the derived subgroup of that stabilizer;
#   * the calculation asks directly whether 10-dimensional F2 factors occur.
#
# It does NOT identify this M24 permutation module with the Carnahan--Urano
# 2B Tate multiplicity.  That same-object identification remains separate.

if LoadPackage("atlasrep") <> true then
  Error("AtlasRep is required");
fi;

expectedM24Order := 244823040;
expectedM22Order := 443520;
expectedM22d2Order := 887040;
expectedDegree := 276;

infos := AllAtlasGeneratingSetInfos("M24");
permInfos := Filtered(infos, info ->
  IsBound(info.repname)
  and PositionSublist(info.repname,"p276") <> fail);

if Length(permInfos)=0 then
  Error("AtlasRep exposes no M24 permutation representation on 276 points");
fi;

info := permInfos[1];
G := AtlasGroup(info);
if G=fail then
  Error("failed to construct M24 p276 representation");
fi;
if Size(G)<>expectedM24Order then
  Error("unexpected M24 order");
fi;
if LargestMovedPoint(G)<>expectedDegree then
  Error("unexpected M24 permutation degree");
fi;

H2 := Stabilizer(G,1);
if Size(H2)<>expectedM22d2Order then
  Error("point stabilizer is not M22:2 of expected order");
fi;

H := DerivedSubgroup(H2);
if Size(H)<>expectedM22Order then
  Error("derived point stabilizer is not M22 of expected order");
fi;

F := GF(2);
moduleH2 := PermutationGModule(H2,F);
moduleH := PermutationGModule(H,F);

if moduleH2.dimension<>expectedDegree or moduleH.dimension<>expectedDegree then
  Error("restricted permutation module does not have dimension 276");
fi;

factorsH2 := MTX.CompositionFactors(moduleH2);
factorsH := MTX.CompositionFactors(moduleH);

dimsH2 := List(factorsH2, f -> f.dimension);
dimsH := List(factorsH, f -> f.dimension);

tenCountH2 := Number(dimsH2,d -> d=10);
tenCountH := Number(dimsH,d -> d=10);

# If 10-dimensional M22 factors occur, identify them against the actual
# AtlasRep f2r10 representations.  Transport each AtlasRep matrix action back
# along an explicit group isomorphism H -> G10 so the MeatAxe modules use the
# same abstract H generators before applying MTX.IsomorphismModules.
tenFactorsH := Filtered(factorsH,f -> f.dimension=10);
m22TenInfos := Filtered(AllAtlasGeneratingSetInfos("M22"), info ->
  IsBound(info.repname) and PositionSublist(info.repname,"f2r10") <> fail);
identifiedTenFactors := [];

for factor in tenFactorsH do
  labels := [];
  for tenInfo in m22TenInfos do
    G10 := AtlasGroup(tenInfo);
    if G10<>fail and Size(G10)=expectedM22Order then
      iso := IsomorphismGroups(H,G10);
      if iso<>fail then
        transportedMats := List(GeneratorsOfGroup(H), h -> Image(iso,h));
        transportedModule := GModuleByMats(transportedMats,F);
        if MTX.IsomorphismModules(factor,transportedModule)<>fail then
          Add(labels,tenInfo.repname);
        fi;
      fi;
    fi;
  od;
  Add(identifiedTenFactors,labels);
od;

orbitsH2 := Orbits(H2,[1..expectedDegree]);
orbitsH := Orbits(H,[1..expectedDegree]);

PrintNatList := function(out,xs)
  local i;
  AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i>1 then AppendTo(out,","); fi;
    AppendTo(out,String(xs[i]));
  od;
  AppendTo(out,"]");
end;

PrintStringList := function(out,xs)
  local i;
  AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i>1 then AppendTo(out,","); fi;
    AppendTo(out,"\"",xs[i],"\"");
  od;
  AppendTo(out,"]");
end;

PrintNestedStringLists := function(out,xss)
  local i;
  AppendTo(out,"[");
  for i in [1..Length(xss)] do
    if i>1 then AppendTo(out,","); fi;
    PrintStringList(out,xss[i]);
  od;
  AppendTo(out,"]");
end;

output := OutputTextFile("build/m24_276_to_m22_f2_composition_screen.json",false);
SetPrintFormattingStatus(output,false);
AppendTo(output,"{\n");
AppendTo(output,"  \"atlas_repname\": \"",info.repname,"\",\n");
AppendTo(output,"  \"m24_order\": ",String(Size(G)),",\n");
AppendTo(output,"  \"permutation_degree\": ",String(expectedDegree),",\n");
AppendTo(output,"  \"m22d2_order\": ",String(Size(H2)),",\n");
AppendTo(output,"  \"m22_order\": ",String(Size(H)),",\n");
AppendTo(output,"  \"m22d2_orbit_sizes\": ");
PrintNatList(output,List(orbitsH2,Length));
AppendTo(output,",\n");
AppendTo(output,"  \"m22_orbit_sizes\": ");
PrintNatList(output,List(orbitsH,Length));
AppendTo(output,",\n");
AppendTo(output,"  \"m22d2_factor_dimensions\": ");
PrintNatList(output,dimsH2);
AppendTo(output,",\n");
AppendTo(output,"  \"m22_factor_dimensions\": ");
PrintNatList(output,dimsH);
AppendTo(output,",\n");
AppendTo(output,"  \"m22d2_dimension_sum\": ",String(Sum(dimsH2)),",\n");
AppendTo(output,"  \"m22_dimension_sum\": ",String(Sum(dimsH)),",\n");
AppendTo(output,"  \"m22d2_ten_factor_count\": ",String(tenCountH2),",\n");
AppendTo(output,"  \"m22_ten_factor_count\": ",String(tenCountH),",\n");
AppendTo(output,"  \"m22_ten_factor_atlasrep_matches\": ");
PrintNestedStringLists(output,identifiedTenFactors);
AppendTo(output,"\n");
AppendTo(output,"}\n");
CloseStream(output);

Print("M24 p276 -> M22:2/M22 F2 screen written. ",
  "M22:2 10-factors=",tenCountH2,
  "; M22 10-factors=",tenCountH,"\n");
QUIT;
