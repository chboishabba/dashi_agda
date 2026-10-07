# Verify directly over GF(2) that the exterior square of the natural M24
# 24-point permutation module is the degree-276 duad permutation module.
#
# In characteristic two the exterior-square basis e_i wedge e_j (i<j) is
# permuted without signs, so this is the literal 2-subset action.  To compare
# with the Atlas p276 representation we do more than compare abstract groups:
# under an isomorphism ExtG -> G276, the point stabilizer of the exterior action
# must be conjugate to the Atlas p276 point stabilizer.  For transitive actions
# this certifies equivalence of the permutation representations.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
F:=GF(2); n:=24; d:=276;

p24Infos:=Filtered(AllAtlasGeneratingSetInfos("M24"),info -> IsBound(info.repname) and PositionSublist(info.repname,"p24")<>fail);
p276Infos:=Filtered(AllAtlasGeneratingSetInfos("M24"),info -> IsBound(info.repname) and PositionSublist(info.repname,"p276")<>fail);
if Length(p24Infos)=0 or Length(p276Infos)=0 then Error("need M24 p24 and p276"); fi;
G24:=AtlasGroup(p24Infos[1]); G276:=AtlasGroup(p276Infos[1]);
if G24=fail or G276=fail then Error("failed to construct M24 Atlas actions"); fi;

pairs:=[];
for i in [1..n] do for j in [i+1..n] do Add(pairs,[i,j]); od; od;
if Length(pairs)<>d then Error("pair count not 276"); fi;
PairPos:=function(a,b)
  local x,y;
  if a<b then x:=a; y:=b; else x:=b; y:=a; fi;
  return Position(pairs,[x,y]);
end;

ExteriorPermutation:=function(g)
  local imgs,k,p;
  imgs:=[];
  for k in [1..d] do
    p:=pairs[k]; Add(imgs,PairPos(p[1]^g,p[2]^g));
  od;
  return PermList(imgs);
end;

ExtG:=Group(List(GeneratorsOfGroup(G24),ExteriorPermutation));
if Size(ExtG)<>244823040 then Error("exterior-square action not faithful M24"); fi;
if not IsTransitive(ExtG,[1..d]) or not IsTransitive(G276,[1..d]) then Error("expected transitive degree-276 actions"); fi;
isoExt:=IsomorphismGroups(ExtG,G276);
if isoExt=fail then Error("exterior-square 276 not abstractly isomorphic to Atlas p276 action"); fi;

stabExt:=Stabilizer(ExtG,1);
stabAtlas:=Stabilizer(G276,1);
if Size(stabExt)<>887040 or Size(stabAtlas)<>887040 then Error("degree-276 point stabilizer is not M22:2 order"); fi;
imageStabExt:=Image(isoExt,stabExt);
stabilizersConjugate:=IsConjugate(G276,imageStabExt,stabAtlas);
if not stabilizersConjugate then
  Error("exterior-square and Atlas p276 transitive actions have nonconjugate point stabilizers");
fi;

Mext:=PermutationGModule(ExtG,F);
factors:=MTX.CompositionFactors(Mext);
series:=MTX.BasesCompositionSeries(Mext);
rad:=MTX.BasisRadical(Mext);
soc:=MTX.BasisSocle(Mext);
endos:=MTX.BasisModuleEndomorphisms(Mext);

PrintNatList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;
JsonBool:=function(x) if x then return "true"; else return "false"; fi; end;

out:=OutputTextFile("build/m24_exterior_square24_duad276_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"pair_count\":276,\n");
AppendTo(out,"  \"exterior_action_order\":",String(Size(ExtG)),",\n");
AppendTo(out,"  \"atlas_p276_action_order\":",String(Size(G276)),",\n");
AppendTo(out,"  \"point_stabilizer_order\":",String(Size(stabExt)),",\n");
AppendTo(out,"  \"point_stabilizers_conjugate\":",JsonBool(stabilizersConjugate),",\n");
AppendTo(out,"  \"permutation_representations_equivalent\":true,\n");
AppendTo(out,"  \"composition_factor_dimensions\":"); PrintNatList(out,List(factors,f->MTX.Dimension(f))); AppendTo(out,",\n");
AppendTo(out,"  \"composition_series_dimensions\":"); PrintNatList(out,List(series,Length)); AppendTo(out,",\n");
AppendTo(out,"  \"radical_dimension\":",String(Length(rad)),",\n");
AppendTo(out,"  \"socle_dimension\":",String(Length(soc)),",\n");
AppendTo(out,"  \"endomorphism_algebra_dimension\":",String(Length(endos)),",\n");
AppendTo(out,"  \"actual_2b_tate_identified\":false\n}\n");
CloseStream(out);
Print("M24 exterior-square24/duad276 screen: permutation-equivalent; factors=",List(factors,f->MTX.Dimension(f)),"\n");
QUIT;
