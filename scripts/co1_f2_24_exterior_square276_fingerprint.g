# Construct the exterior square of the actual AtlasRep 24-dimensional GF(2)
# Co1 module and compute its 276-dimensional modular extension fingerprint.
#
# Besides raw dimensions, identify every nontrivial composition factor against
# the actual AtlasRep 274-dimensional GF(2) Co1 module and expose radical,
# socle, endomorphism and indecomposability data.  This tests whether wedge2(24)
# is the expected nonsemisimple 1/274/1-type object rather than treating 276 as
# a dimension coincidence.
#
# This is still only a finite Co1 candidate.  It does NOT prove that the normal
# 2^24 in the 2B modular-moonshine group acts trivially on the actual Tate head.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
F:=GF(2); n:=24; d:=276;

infos:=AllAtlasGeneratingSetInfos("Co1",Dimension,24,Characteristic,2);
if Length(infos)=0 then Error("AtlasRep exposes no Co1 24d GF2 module"); fi;
G24:=AtlasGroup(infos[1]);
if G24=fail then Error("failed to construct Co1 24d GF2 module"); fi;
if Size(G24)<>4157776806543360000 then Error("unexpected Co1 order"); fi;
gens24:=GeneratorsOfGroup(G24);
if NrRows(gens24[1])<>24 then Error("unexpected 24d generator size"); fi;

infos274:=AllAtlasGeneratingSetInfos("Co1",Dimension,274,Characteristic,2);
if Length(infos274)=0 then Error("AtlasRep exposes no Co1 274d GF2 module"); fi;
G274:=AtlasGroup(infos274[1]);
if G274=fail or Size(G274)<>Size(G24) then Error("failed Co1 274d Atlas module"); fi;
M274:=GModuleByMats(GeneratorsOfGroup(G274),F);

pairs:=[];
for i in [1..n] do for j in [i+1..n] do Add(pairs,[i,j]); od; od;
if Length(pairs)<>d then Error("pair count not 276"); fi;

ExtMat:=function(A)
  local rows,ij,pq,row,i,j,p,q,c;
  rows:=[];
  for ij in pairs do
    i:=ij[1]; j:=ij[2]; row:=[];
    for pq in pairs do
      p:=pq[1]; q:=pq[2];
      c:=A[i][p]*A[j][q] + A[i][q]*A[j][p];
      Add(row,c);
    od;
    Add(rows,row);
  od;
  return ImmutableMatrix(F,rows);
end;

gens276:=List(gens24,ExtMat);
G276:=Group(gens276);
if Size(G276)<>Size(G24) then Error("exterior-square action is not faithful Co1"); fi;
M:=GModuleByMats(gens276,F);
if MTX.Dimension(M)<>276 then Error("exterior-square module is not dimension 276"); fi;

factors:=MTX.CompositionFactors(M);
series:=MTX.BasesCompositionSeries(M);
rad:=MTX.BasisRadical(M);
soc:=MTX.BasisSocle(M);
endos:=MTX.BasisModuleEndomorphisms(M);
indecomp:=MTX.Indecomposition(M);

IsTrivialFactor:=function(X)
  local one;
  if MTX.Dimension(X)<>1 then return false; fi;
  one:=IdentityMat(1,F);
  return ForAll(X.generators,g -> g=one);
end;

factorKinds:=[];
trivialFactorCount:=0;
atlas274FactorCount:=0;
unidentifiedFactorCount:=0;
for X in factors do
  if IsTrivialFactor(X) then
    Add(factorKinds,"1"); trivialFactorCount:=trivialFactorCount+1;
  elif MTX.Dimension(X)=274 and MTX.IsomorphismModules(X,M274)<>fail then
    Add(factorKinds,"274"); atlas274FactorCount:=atlas274FactorCount+1;
  else
    Add(factorKinds,Concatenation("unidentified-",String(MTX.Dimension(X))));
    unidentifiedFactorCount:=unidentifiedFactorCount+1;
  fi;
od;

PrintNatList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;
PrintStringList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,"\"",xs[i],"\""); od;
  AppendTo(out,"]");
end;
JsonBool:=function(x) if x then return "true"; else return "false"; fi; end;

indecompDims:=List(indecomp,x->MTX.Dimension(x[2]));
moduleIndecomposable:=Length(indecomp)=1;

out:=OutputTextFile("build/co1_f2_24_exterior_square276_fingerprint.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"co1_order\":",String(Size(G24)),",\n");
AppendTo(out,"  \"source_module_dimension\":24,\n");
AppendTo(out,"  \"exterior_square_dimension\":276,\n");
AppendTo(out,"  \"composition_factor_dimensions\":"); PrintNatList(out,List(factors,f->MTX.Dimension(f))); AppendTo(out,",\n");
AppendTo(out,"  \"composition_factor_kinds\":"); PrintStringList(out,factorKinds); AppendTo(out,",\n");
AppendTo(out,"  \"trivial_factor_count\":",String(trivialFactorCount),",\n");
AppendTo(out,"  \"atlas_274_factor_count\":",String(atlas274FactorCount),",\n");
AppendTo(out,"  \"unidentified_factor_count\":",String(unidentifiedFactorCount),",\n");
AppendTo(out,"  \"composition_series_dimensions\":"); PrintNatList(out,List(series,Length)); AppendTo(out,",\n");
AppendTo(out,"  \"radical_dimension\":",String(Length(rad)),",\n");
AppendTo(out,"  \"socle_dimension\":",String(Length(soc)),",\n");
AppendTo(out,"  \"endomorphism_algebra_dimension\":",String(Length(endos)),",\n");
AppendTo(out,"  \"indecomposable_dimensions\":"); PrintNatList(out,indecompDims); AppendTo(out,",\n");
AppendTo(out,"  \"module_indecomposable\":",JsonBool(moduleIndecomposable),",\n");
AppendTo(out,"  \"one_274_one_composition_profile\":",JsonBool(trivialFactorCount=2 and atlas274FactorCount=1 and unidentifiedFactorCount=0),",\n");
AppendTo(out,"  \"normal_2pow24_triviality_on_tate_proved\":false,\n");
AppendTo(out,"  \"actual_2b_tate_identified_with_exterior_square\":false\n}\n");
CloseStream(out);
Print("Co1 GF2 exterior-square276 fingerprint: kinds=",factorKinds,
  "; rad=",Length(rad),"; soc=",Length(soc),"; end=",Length(endos),
  "; indecomp=",indecompDims,"\n");
QUIT;
