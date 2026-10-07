# Construct the ATLAS maximal subgroup 2^10:M22:2 < Fi22:2 and extract the
# conjugation action of the quotient M22:2 on its normal elementary-abelian
# 2^10 kernel.  This produces a source-native ten-dimensional GF(2) module,
# which is then identified against the actual AtlasRep M22:2 10d modules and
# screened for the outer J2^5 Completion10 fingerprint.
#
# This is a finite/source donor only.  It does NOT identify the Fi22:2 normal
# 2^10 kernel with a subquotient of the actual Monster 2B Tate head.

if LoadPackage("atlasrep") <> true then
  Error("AtlasRep is required");
fi;

expectedFi22d2Order := 129123503308800;
expectedMaxOrder := 908328960;
expectedKernelOrder := 1024;
expectedQuotientOrder := 887040;
expectedDimension := 10;
F := GF(2);

# ATLAS/GAP name is F22.2 in AtlasRep.  Use the primitive 3510-point action,
# for which the fourth maximal subgroup is 2^10:M22:2.
G := AtlasGroup("F22.2", NrMovedPoints, 3510);
if G=fail then
  Error("failed to construct Fi22:2 degree-3510 ATLAS representation");
fi;
if Size(G)<>expectedFi22d2Order then
  Error("unexpected Fi22:2 order");
fi;

S := AtlasSubgroup(G,4);
if S=fail then
  Error("failed to construct fourth Fi22:2 maximal subgroup");
fi;
if Size(S)<>expectedMaxOrder then
  Error("fourth maximal subgroup is not 2^10:M22:2 of expected order");
fi;

N := FittingSubgroup(S);
if Size(N)<>expectedKernelOrder then
  Error("Fitting subgroup is not the expected normal 2^10");
fi;
if not IsElementaryAbelian(N) then
  Error("normal 2^10 kernel is not elementary abelian");
fi;

nat := NaturalHomomorphismByNormalSubgroup(S,N);
Q := Image(nat);
if Size(Q)<>expectedQuotientOrder then
  Error("quotient by 2^10 is not M22:2 of expected order");
fi;

basis := Pcgs(N);
if Length(basis)<>expectedDimension then
  Error("normal 2^10 does not expose a length-10 pcgs basis");
fi;

gensQ := GeneratorsOfGroup(Q);
lifts := List(gensQ,q -> PreImagesRepresentative(nat,q));

ActionMatrix := function(g)
  local rows,b,exps;
  rows := [];
  for b in basis do
    exps := ExponentsOfPcElement(basis,b^g);
    Add(rows,List(exps,e -> e*One(F)));
  od;
  return ImmutableMatrix(F,rows);
end;

mats := List(lifts,ActionMatrix);
naturalModule := GModuleByMats(mats,F);
if naturalModule.dimension<>expectedDimension then
  Error("natural 2^10 conjugation module is not 10-dimensional");
fi;

m22d2TenInfos := AllAtlasGeneratingSetInfos(
  "M22.2", Dimension, expectedDimension, Characteristic, 2 );
if Length(m22d2TenInfos)=0 then
  Error("AtlasRep exposes no M22:2 dimension-10 GF(2) representations");
fi;

atlasMatches := [];
for info in m22d2TenInfos do
  G10 := AtlasGroup(info);
  if G10<>fail and Size(G10)=expectedQuotientOrder then
    iso := IsomorphismGroups(Q,G10);
    if iso<>fail then
      transportedMats := List(gensQ,q -> Image(iso,q));
      transportedModule := GModuleByMats(transportedMats,F);
      if MTX.IsomorphismModules(naturalModule,transportedModule)<>fail then
        Add(atlasMatches,info.repname);
      fi;
    fi;
  fi;
od;
if Length(atlasMatches)=0 then
  Error("natural Fi22:2 2^10 module did not match any Atlas M22:2 10d module");
fi;

MG := Group(mats);
rho := GroupHomomorphismByImages(Q,MG,gensQ,mats);
if rho=fail or not IsGroupHomomorphism(rho) then
  Error("failed to build quotient action homomorphism on normal 2^10");
fi;

D := DerivedSubgroup(Q);
if Size(D)<>443520 then
  Error("derived quotient is not M22 of expected order");
fi;

classes := ConjugacyClasses(Q);
involutionClasses := Filtered(classes,cl -> Order(Representative(cl))=2);
outerRows := [];
outerJ2x5Count := 0;
for cl in involutionClasses do
  q := Representative(cl);
  if not (q in D) then
    m := Image(rho,q);
    id := One(m);
    rankDiff := RankMat(m-id);
    fixedDim := expectedDimension-rankDiff;
    squareZero := (m-id)*(m-id)=Zero(m);
    match := rankDiff=5 and fixedDim=5 and squareZero;
    if match then outerJ2x5Count := outerJ2x5Count+1; fi;
    Add(outerRows,[Size(cl),Size(Q)/Size(cl),rankDiff,fixedDim,squareZero,match]);
  fi;
od;

JsonBool := function(x)
  if x then return "true"; else return "false"; fi;
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

PrintOuterRows := function(out,rows)
  local i,r;
  AppendTo(out,"[");
  for i in [1..Length(rows)] do
    if i>1 then AppendTo(out,","); fi;
    r := rows[i];
    AppendTo(out,"{\"class_size\":",String(r[1]),
      ",\"centralizer_order\":",String(r[2]),
      ",\"rank_g_minus_i\":",String(r[3]),
      ",\"fixed_dimension\":",String(r[4]),
      ",\"square_zero\":",JsonBool(r[5]),
      ",\"matches_J2x5\":",JsonBool(r[6]),"}");
  od;
  AppendTo(out,"]");
end;

out := OutputTextFile(
  "build/fi22d2_2pow10_m22d2_natural_module_screen.json", false );
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"fi22d2_order\": ",String(Size(G)),",\n");
AppendTo(out,"  \"maximal_subgroup_order\": ",String(Size(S)),",\n");
AppendTo(out,"  \"normal_kernel_order\": ",String(Size(N)),",\n");
AppendTo(out,"  \"normal_kernel_elementary_abelian\": true,\n");
AppendTo(out,"  \"quotient_order\": ",String(Size(Q)),",\n");
AppendTo(out,"  \"natural_module_dimension\": ",String(naturalModule.dimension),",\n");
AppendTo(out,"  \"atlas_m22d2_10d_matches\": ");
PrintStringList(out,atlasMatches);
AppendTo(out,",\n");
AppendTo(out,"  \"outer_involution_rows\": ");
PrintOuterRows(out,outerRows);
AppendTo(out,",\n");
AppendTo(out,"  \"outer_J2x5_match_count\": ",String(outerJ2x5Count),",\n");
AppendTo(out,"  \"finite_source_native_completion10_module_identified\": ",
  JsonBool(Length(atlasMatches)>0 and outerJ2x5Count>0),",\n");
AppendTo(out,"  \"actual_2b_tate_same_object_identified\": false\n");
AppendTo(out,"}\n");
CloseStream(out);

Print("Fi22:2 2^10:M22:2 natural-module screen written: Atlas matches=",
  Length(atlasMatches),"; outer J2^5 matches=",outerJ2x5Count,"\n");
QUIT;
