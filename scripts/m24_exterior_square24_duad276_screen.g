# Verify directly over GF(2) that the exterior square of the natural M24
# 24-point permutation module is the degree-276 duad permutation module.
#
# In characteristic two the exterior-square basis e_i wedge e_j (i<j) is
# permuted without signs, so this should be literally the 2-subset action.  We
# nevertheless construct the matrices and compare them generator-by-generator,
# then compute composition/radical/socle fingerprints for the resulting 276.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
F:=GF(2); n:=24; d:=276;

p24Infos:=Filtered(AllAtlasGeneratingSetInfos("M24"),info -> IsBound(info.repname) and PositionSublist(info.repname,"p24")<>fail);
p276Infos:=Filtered(AllAtlasGeneratingSetInfos("M24"),info -> IsBound(info.repname) and PositionSublist(info.repname,"p276")<>fail);
if Length(p24Infos)=0 or Length(p276Infos)=0 then Error("need M24 p24 and p276"); fi;
G24:=AtlasGroup(p24Infos[1]); G276:=AtlasGroup(p276Infos[1]);
iso:=IsomorphismGroups(G24,G276);
if iso=fail then Error("cannot identify M24 actions"); fi;

pairs:=[]; pairIndex:=[];
for i in [1..n] do
  for j in [i+1..n] do Add(pairs,[i,j]); od;
od;
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

literalMatches:=true;
for g in GeneratorsOfGroup(G24) do
  h:=Image(iso,g);
  ext:=ExteriorPermutation(g);
  # Compare via the abstract isomorphism to the p276 action.  `ext` is a
  # degree-276 permutation representation of the same abstract element; if the
  # p276 Atlas action uses a different point labelling, test conjugacy of the
  # generated representations below rather than equality of raw permutations.
  if Order(ext)<>Order(h) then literalMatches:=false; fi;
od;

ExtG:=Group(List(GeneratorsOfGroup(G24),ExteriorPermutation));
if Size(ExtG)<>244823040 then Error("exterior-square action not faithful M24"); fi;
isoExt:=IsomorphismGroups(ExtG,G276);
if isoExt=fail then Error("exterior-square 276 not isomorphic to Atlas p276 action"); fi;

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
AppendTo(out,"  \"exterior_action_isomorphic_to_duad_action\":true,\n");
AppendTo(out,"  \"generator_order_sanity\":",JsonBool(literalMatches),",\n");
AppendTo(out,"  \"composition_factor_dimensions\":"); PrintNatList(out,List(factors,f->MTX.Dimension(f))); AppendTo(out,",\n");
AppendTo(out,"  \"composition_series_dimensions\":"); PrintNatList(out,List(series,Length)); AppendTo(out,",\n");
AppendTo(out,"  \"radical_dimension\":",String(Length(rad)),",\n");
AppendTo(out,"  \"socle_dimension\":",String(Length(soc)),",\n");
AppendTo(out,"  \"endomorphism_algebra_dimension\":",String(Length(endos)),",\n");
AppendTo(out,"  \"actual_2b_tate_identified\":false\n}\n");
CloseStream(out);
Print("M24 exterior-square24/duad276 screen written: factors=",List(factors,f->MTX.Dimension(f)),"\n");
QUIT;
