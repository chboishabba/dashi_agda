# Identify explicit ten-dimensional M22:2-stable subquotients of the actual
# M24 degree-276 duad permutation module, and test the outer Completion10 action
# on EVERY such quotient.
#
# MeatAxe supplies both:
#   * BasesCompositionSeries(moduleH2): literal invariant subspaces
#       0 = M0 < M1 < ... < Mk = F2^276,
#   * CompositionFactors(moduleH2): quotient modules Mi+1/Mi in the same order.
#
# Every 10-dimensional quotient is AtlasRep-identified and screened for outer
# J2^5.  We retain one matching quotient with its literal N<=S bases and induced
# 10x10 matrices, while also recording whether that matching quotient is unique
# among the observed 10d composition-series steps.
#
# This closes finite-model B'+C' on one and the same duad quotient.  It still
# does NOT identify this N<=S chain with an actual subquotient of the Monster 2B
# Tate head: the CTblLib Brauer PASS pays only semisimplified/Jordan-Hoelder
# ingress, not characteristic-two extension data.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;

expectedM24Order := 244823040;
expectedM22d2Order := 887040;
expectedM22Order := 443520;
expectedDegree := 276;
expectedTenDimension := 10;
F := GF(2);

infos := AllAtlasGeneratingSetInfos("M24");
permInfos := Filtered(infos, info ->
  IsBound(info.repname) and PositionSublist(info.repname,"p276") <> fail);
if Length(permInfos)=0 then Error("AtlasRep exposes no M24 p276 permutation representation"); fi;
info := permInfos[1];
G := AtlasGroup(info);
if G=fail or Size(G)<>expectedM24Order then Error("failed to construct expected M24 p276 representation"); fi;
if LargestMovedPoint(G)<>expectedDegree then Error("unexpected M24 p276 degree"); fi;

H2 := Stabilizer(G,1);
if Size(H2)<>expectedM22d2Order then Error("point stabilizer is not M22:2 of expected order"); fi;
moduleH2 := PermutationGModule(H2,F);
if moduleH2.dimension<>expectedDegree then Error("M22:2 restricted permutation module does not have dimension 276"); fi;

seriesH2 := MTX.BasesCompositionSeries(moduleH2);
factorsH2 := MTX.CompositionFactors(moduleH2);
if Length(seriesH2)<>Length(factorsH2)+1 then Error("composition-series/factor lengths are not aligned"); fi;
factorDims := List(factorsH2,f -> f.dimension);
seriesDims := List(seriesH2,Length);
seriesFactorDims := List([1..Length(factorsH2)],i -> seriesDims[i+1]-seriesDims[i]);
if factorDims<>seriesFactorDims then Error("composition factor dimensions do not match adjacent series steps"); fi;

tenFactorIndices := Filtered([1..Length(factorsH2)],i -> factorsH2[i].dimension=expectedTenDimension);
if Length(tenFactorIndices)=0 then Error("M22:2 duad-276 module has no 10-dimensional composition factor"); fi;

m22d2TenInfos := AllAtlasGeneratingSetInfos("M22.2",Dimension,expectedTenDimension,Characteristic,2);
if Length(m22d2TenInfos)=0 then Error("AtlasRep exposes no M22:2 dimension-10 GF(2) representations"); fi;

JsonBool := function(x) if x then return "true"; else return "false"; fi; end;

# Atlas identification and outer-J2^5 screen for each observed 10d quotient.
factorMatches := [];
factorOuterJ2x5Counts := [];
factorOuterRows := [];
for idx in tenFactorIndices do
  factor := factorsH2[idx];
  labels := [];
  for tenInfo in m22d2TenInfos do
    G10 := AtlasGroup(tenInfo);
    if G10<>fail and Size(G10)=expectedM22d2Order then
      iso := IsomorphismGroups(H2,G10);
      if iso<>fail then
        transportedMats := List(GeneratorsOfGroup(H2), h -> Image(iso,h));
        transportedModule := GModuleByMats(transportedMats,F);
        if MTX.IsomorphismModules(factor,transportedModule)<>fail then Add(labels,tenInfo.repname); fi;
      fi;
    fi;
  od;
  if Length(labels)=0 then Error("10-dimensional M22:2 factor was not Atlas-identified"); fi;
  Add(factorMatches,labels);

  FG := Group(factor.generators);
  if Size(FG)<>expectedM22d2Order then Error("10d quotient action is not faithful M22:2"); fi;
  FD := DerivedSubgroup(FG);
  if Size(FD)<>expectedM22Order then Error("10d quotient derived subgroup is not M22"); fi;
  rows := [];
  cnt := 0;
  for cl in ConjugacyClasses(FG) do
    gg := Representative(cl);
    if Order(gg)=2 and not (gg in FD) then
      ii := One(gg);
      rr := RankMat(gg-ii);
      ff := expectedTenDimension-rr;
      sq := (gg-ii)*(gg-ii)=Zero(gg);
      mt := rr=5 and ff=5 and sq;
      if mt then cnt:=cnt+1; fi;
      Add(rows,[Size(cl),Size(FG)/Size(cl),rr,ff,sq,mt]);
    fi;
  od;
  Add(factorOuterJ2x5Counts,cnt);
  Add(factorOuterRows,rows);
od;

matchingTenPositions := Filtered([1..Length(tenFactorIndices)],i -> factorOuterJ2x5Counts[i]>0);
if Length(matchingTenPositions)=0 then Error("no duad 10d composition factor has outer J2^5"); fi;

selectedPos := matchingTenPositions[1];
selectedIndex := tenFactorIndices[selectedPos];
selectedFactor := factorsH2[selectedIndex];
selectedLowerBasis := seriesH2[selectedIndex];
selectedUpperBasis := seriesH2[selectedIndex+1];
selectedLowerDimension := Length(selectedLowerBasis);
selectedUpperDimension := Length(selectedUpperBasis);
if selectedUpperDimension-selectedLowerDimension<>expectedTenDimension then Error("selected series step is not ten-dimensional"); fi;
selectedLabels := factorMatches[selectedPos];
selectedOuterRows := factorOuterRows[selectedPos];
selectedOuterJ2x5Count := factorOuterJ2x5Counts[selectedPos];

PrintNatList := function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;
PrintStringList := function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,"\"",xs[i],"\""); od;
  AppendTo(out,"]");
end;
PrintNestedStringLists := function(out,xss)
  local i; AppendTo(out,"[");
  for i in [1..Length(xss)] do if i>1 then AppendTo(out,","); fi; PrintStringList(out,xss[i]); od;
  AppendTo(out,"]");
end;
PrintF2Vector := function(out,v)
  local j; AppendTo(out,"[");
  for j in [1..Length(v)] do if j>1 then AppendTo(out,","); fi; AppendTo(out,String(Int(v[j]))); od;
  AppendTo(out,"]");
end;
PrintF2Matrix := function(out,m)
  local i; AppendTo(out,"[");
  for i in [1..Length(m)] do if i>1 then AppendTo(out,","); fi; PrintF2Vector(out,m[i]); od;
  AppendTo(out,"]");
end;
PrintF2MatrixList := function(out,ms)
  local i; AppendTo(out,"[");
  for i in [1..Length(ms)] do if i>1 then AppendTo(out,","); fi; PrintF2Matrix(out,ms[i]); od;
  AppendTo(out,"]");
end;
PrintPermutationImages := function(out,g) PrintNatList(out,List([1..expectedDegree],i -> i^g)); end;
PrintPermutationGeneratorList := function(out,gens)
  local i; AppendTo(out,"[");
  for i in [1..Length(gens)] do if i>1 then AppendTo(out,","); fi; PrintPermutationImages(out,gens[i]); od;
  AppendTo(out,"]");
end;
PrintOuterRows := function(out,rows)
  local i,r; AppendTo(out,"[");
  for i in [1..Length(rows)] do
    if i>1 then AppendTo(out,","); fi; r:=rows[i];
    AppendTo(out,"{\"class_size\":",String(r[1]),",\"centralizer_order\":",String(r[2]),
      ",\"rank_g_minus_i\":",String(r[3]),",\"fixed_dimension\":",String(r[4]),
      ",\"square_zero\":",JsonBool(r[5]),",\"matches_J2x5\":",JsonBool(r[6]),"}");
  od; AppendTo(out,"]");
end;

out := OutputTextFile("build/m22d2_276_ten_factor_identification_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"m24_repname\":\"",info.repname,"\",\n");
AppendTo(out,"  \"m24_order\":",String(Size(G)),",\n");
AppendTo(out,"  \"m22d2_order\":",String(Size(H2)),",\n");
AppendTo(out,"  \"dimension\":",String(moduleH2.dimension),",\n");
AppendTo(out,"  \"factor_dimensions\":"); PrintNatList(out,factorDims); AppendTo(out,",\n");
AppendTo(out,"  \"composition_series_dimensions\":"); PrintNatList(out,seriesDims); AppendTo(out,",\n");
AppendTo(out,"  \"dimension_sum\":",String(Sum(factorDims)),",\n");
AppendTo(out,"  \"ten_factor_count\":",String(Length(tenFactorIndices)),",\n");
AppendTo(out,"  \"atlas_ten_rep_count\":",String(Length(m22d2TenInfos)),",\n");
AppendTo(out,"  \"ten_factor_atlasrep_matches\":"); PrintNestedStringLists(out,factorMatches); AppendTo(out,",\n");
AppendTo(out,"  \"ten_factor_outer_J2x5_counts\":"); PrintNatList(out,factorOuterJ2x5Counts); AppendTo(out,",\n");
AppendTo(out,"  \"completion10_matching_ten_factor_count\":",String(Length(matchingTenPositions)),",\n");
AppendTo(out,"  \"completion10_matching_ten_factor_unique\":",JsonBool(Length(matchingTenPositions)=1),",\n");
AppendTo(out,"  \"every_ten_factor_identified\":true,\n");
AppendTo(out,"  \"selected_factor_index\":",String(selectedIndex),",\n");
AppendTo(out,"  \"selected_lower_dimension\":",String(selectedLowerDimension),",\n");
AppendTo(out,"  \"selected_upper_dimension\":",String(selectedUpperDimension),",\n");
AppendTo(out,"  \"selected_factor_atlasrep_matches\":"); PrintStringList(out,selectedLabels); AppendTo(out,",\n");
AppendTo(out,"  \"selected_lower_basis\":"); PrintF2Matrix(out,selectedLowerBasis); AppendTo(out,",\n");
AppendTo(out,"  \"selected_upper_basis\":"); PrintF2Matrix(out,selectedUpperBasis); AppendTo(out,",\n");
AppendTo(out,"  \"ambient_m22d2_generator_permutations\":"); PrintPermutationGeneratorList(out,GeneratorsOfGroup(H2)); AppendTo(out,",\n");
AppendTo(out,"  \"selected_quotient_generators\":"); PrintF2MatrixList(out,selectedFactor.generators); AppendTo(out,",\n");
AppendTo(out,"  \"selected_outer_involution_rows\":"); PrintOuterRows(out,selectedOuterRows); AppendTo(out,",\n");
AppendTo(out,"  \"selected_outer_J2x5_match_count\":",String(selectedOuterJ2x5Count),",\n");
AppendTo(out,"  \"finite_duad_same_quotient_Bprime_Cprime_paid\":true,\n");
AppendTo(out,"  \"actual_2b_tate_stable_subquotient_identified\":false\n}\n");
CloseStream(out);

Print("M22:2 duad-276 stable ten-subquotient screen: factors=",Length(factorsH2),
  "; ten=",Length(tenFactorIndices),"; Completion10 ten-factors=",Length(matchingTenPositions),
  "; selected=",selectedLowerDimension,"->",selectedUpperDimension,"\n");
QUIT;
