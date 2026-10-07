# Identify the 10-dimensional composition factors of the full characteristic-two
# M22:2 action on the actual M24 degree-276 duad permutation module.
#
# This is the strongest finite-model B'+C' screen available before an actual
# Tate<->duad extension weld: the source 276 module is restricted to H2=M22:2,
# its MeatAxe composition factors are computed, and every 10-dimensional factor
# is compared M22:2-equivariantly against the actual AtlasRep f2r10 modules.
#
# If a factor matches one of those Atlas modules, the already-executed outer
# involution screen applies to that factor as an M22:2-module.  This still does
# NOT identify the factor with a literal subquotient of the actual 2B Tate head;
# the CTblLib Brauer screen only pays semisimplified/Jordan-Hoelder ingress.

if LoadPackage("atlasrep") <> true then
  Error("AtlasRep is required");
fi;

expectedM24Order := 244823040;
expectedM22d2Order := 887040;
expectedDegree := 276;
expectedTenDimension := 10;
F := GF(2);

infos := AllAtlasGeneratingSetInfos("M24");
permInfos := Filtered(infos, info ->
  IsBound(info.repname)
  and PositionSublist(info.repname,"p276") <> fail);
if Length(permInfos)=0 then
  Error("AtlasRep exposes no M24 permutation representation on 276 points");
fi;

info := permInfos[1];
G := AtlasGroup(info);
if G=fail or Size(G)<>expectedM24Order then
  Error("failed to construct expected M24 p276 representation");
fi;
if LargestMovedPoint(G)<>expectedDegree then
  Error("unexpected M24 p276 degree");
fi;

H2 := Stabilizer(G,1);
if Size(H2)<>expectedM22d2Order then
  Error("point stabilizer is not M22:2 of expected order");
fi;

moduleH2 := PermutationGModule(H2,F);
if moduleH2.dimension<>expectedDegree then
  Error("M22:2 restricted permutation module does not have dimension 276");
fi;

factorsH2 := MTX.CompositionFactors(moduleH2);
tenFactorsH2 := Filtered(factorsH2,f -> f.dimension=expectedTenDimension);

m22d2TenInfos := AllAtlasGeneratingSetInfos(
  "M22.2", Dimension, expectedTenDimension, Characteristic, 2 );
if Length(m22d2TenInfos)=0 then
  Error("AtlasRep exposes no M22:2 dimension-10 GF(2) representations");
fi;

factorMatches := [];
for factor in tenFactorsH2 do
  labels := [];
  for tenInfo in m22d2TenInfos do
    G10 := AtlasGroup(tenInfo);
    if G10<>fail and Size(G10)=expectedM22d2Order then
      iso := IsomorphismGroups(H2,G10);
      if iso<>fail then
        transportedMats := List(GeneratorsOfGroup(H2), h -> Image(iso,h));
        transportedModule := GModuleByMats(transportedMats,F);
        if MTX.IsomorphismModules(factor,transportedModule)<>fail then
          Add(labels,tenInfo.repname);
        fi;
      fi;
    fi;
  od;
  Add(factorMatches,labels);
od;

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

out := OutputTextFile(
  "build/m22d2_276_ten_factor_identification_screen.json", false );
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"m24_repname\": \"",info.repname,"\",\n");
AppendTo(out,"  \"m24_order\": ",String(Size(G)),",\n");
AppendTo(out,"  \"m22d2_order\": ",String(Size(H2)),",\n");
AppendTo(out,"  \"dimension\": ",String(moduleH2.dimension),",\n");
AppendTo(out,"  \"factor_dimensions\": ");
PrintNatList(out,List(factorsH2,f -> f.dimension));
AppendTo(out,",\n");
AppendTo(out,"  \"dimension_sum\": ",String(Sum(List(factorsH2,f -> f.dimension))),",\n");
AppendTo(out,"  \"ten_factor_count\": ",String(Length(tenFactorsH2)),",\n");
AppendTo(out,"  \"atlas_ten_rep_count\": ",String(Length(m22d2TenInfos)),",\n");
AppendTo(out,"  \"ten_factor_atlasrep_matches\": ");
PrintNestedStringLists(out,factorMatches);
AppendTo(out,",\n");
AppendTo(out,"  \"every_ten_factor_identified\": ",
  String(ForAll(factorMatches,xs -> Length(xs)>0)),",\n");
AppendTo(out,"  \"finite_duad_m22d2_stable_ten_subquotient_identified\": ",
  String(Length(tenFactorsH2)>0 and ForAll(factorMatches,xs -> Length(xs)>0)),",\n");
AppendTo(out,"  \"actual_2b_tate_stable_subquotient_identified\": false\n");
AppendTo(out,"}\n");
CloseStream(out);

Print("M22:2-on-duad-276 ten-factor screen written: factors=",
  Length(factorsH2),"; ten-factors=",Length(tenFactorsH2),"\n");
QUIT;
