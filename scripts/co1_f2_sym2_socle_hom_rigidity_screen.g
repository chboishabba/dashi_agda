# Prove the target-side uniqueness needed by the shortest 2B norm weld without
# enumerating the full submodule lattice of Sym^2(Co1-24).
#
# We construct Sym2(24) over GF(2), identify its composition-factor dimensions,
# and compute
#
#   Hom_Co1(1,Sym2), Hom_Co1(24,Sym2), Hom_Co1(274,Sym2).
#
# If the factor dimensions are exactly 1,1,24,274, the first and third Hom
# spaces vanish, and the 24-Hom space is one-dimensional, then the socle is a
# single 24-dimensional simple.  The separate Frobenius-Hom screen already
# verifies that the explicit square map spans that unique nonzero 24-Hom line,
# hence the socle is literally the Frobenius image.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
F:=GF(2); n:=24;
expectedCo1Order:=4157776806543360000;

infos24:=AllAtlasGeneratingSetInfos("Co1",Dimension,24,Characteristic,2);
infos274:=AllAtlasGeneratingSetInfos("Co1",Dimension,274,Characteristic,2);
if Length(infos24)=0 or Length(infos274)=0 then
  Error("required Co1 GF2 Atlas modules unavailable");
fi;
G24:=AtlasGroup(infos24[1]);
G274:=AtlasGroup(infos274[1]);
if G24=fail or G274=fail or Size(G24)<>expectedCo1Order or Size(G274)<>expectedCo1Order then
  Error("failed to construct Co1 24/274 modules");
fi;

# AtlasRep standard modules use the same standard-generator convention.  Do
# NOT call IsomorphismGroups on faithful Co1 matrix groups here: that search is
# unnecessary and can dominate the runtime.
gens24:=GeneratorsOfGroup(G24);
gens274:=GeneratorsOfGroup(G274);
if Length(gens24)<>Length(gens274) then
  Error("Co1 standard modules expose different generator counts");
fi;
M24:=GModuleByMats(gens24,F);
M274:=GModuleByMats(gens274,F);

# Trivial module on the same generator count.
trivMats:=List(gens24,g -> ImmutableMatrix(F,[[One(F)]]));
M1:=GModuleByMats(trivMats,F);

symPairs:=[];
for i in [1..n] do for j in [i..n] do Add(symPairs,[i,j]); od; od;
if Length(symPairs)<>300 then Error("Sym2 basis size is not 300"); fi;

SymMat:=function(A)
  local rows,ij,pq,row,i,j,p,q,c;
  rows:=[];
  for ij in symPairs do
    i:=ij[1]; j:=ij[2]; row:=[];
    for pq in symPairs do
      p:=pq[1]; q:=pq[2];
      if p=q then c:=A[i][p]*A[j][p];
      else c:=A[i][p]*A[j][q]+A[i][q]*A[j][p]; fi;
      Add(row,c);
    od;
    Add(rows,row);
  od;
  return ImmutableMatrix(F,rows);
end;

symGens:=List(gens24,SymMat);
Msym:=GModuleByMats(symGens,F);
if MTX.Dimension(Msym)<>300 then Error("Sym2 dimension is not 300"); fi;

factors:=MTX.CompositionFactors(Msym);
factorDims:=SortedList(List(factors,f->MTX.Dimension(f)));
expectedFactorDims:=[1,1,24,274];
if factorDims<>expectedFactorDims then
  Error("unexpected Sym2 composition-factor dimensions");
fi;

hom1:=MTX.BasisModuleHomomorphisms(M1,Msym);
hom24:=MTX.BasisModuleHomomorphisms(M24,Msym);
hom274:=MTX.BasisModuleHomomorphisms(M274,Msym);

hom1Dim:=Length(hom1);
hom24Dim:=Length(hom24);
hom274Dim:=Length(hom274);

if hom1Dim<>0 then Error("Sym2 has a trivial simple submodule"); fi;
if hom274Dim<>0 then Error("Sym2 has a 274-dimensional simple submodule"); fi;
if hom24Dim<>1 then Error("Sym2 does not have a unique 24-Hom line"); fi;
if RankMat(hom24[1])<>24 then Error("unique 24-Hom does not embed the 24-simple"); fi;

# Explicit Frobenius rows and equality to the unique Hom basis over GF(2).
frobRows:=List([1..n],i ->
  List([1..Length(symPairs)],k ->
    if symPairs[k]=[i,i] then One(F) else Zero(F) fi));
frob:=ImmutableMatrix(F,frobRows);
if RankMat(frob)<>24 then Error("Frobenius rank is not 24"); fi;
frobSpans:=hom24[1]=frob;
if not frobSpans then Error("unique 24-Hom is not explicit Frobenius map"); fi;

JsonBool:=function(x) if x then return "true"; else return "false"; fi; end;
PrintNatList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;

out:=OutputTextFile("build/co1_f2_sym2_socle_hom_rigidity_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"co1_order\":",String(Size(G24)),",\n");
AppendTo(out,"  \"sym2_dimension\":300,\n");
AppendTo(out,"  \"composition_factor_dimensions\":"); PrintNatList(out,factorDims); AppendTo(out,",\n");
AppendTo(out,"  \"hom_1_to_sym2_dimension\":",String(hom1Dim),",\n");
AppendTo(out,"  \"hom_24_to_sym2_dimension\":",String(hom24Dim),",\n");
AppendTo(out,"  \"hom_274_to_sym2_dimension\":",String(hom274Dim),",\n");
AppendTo(out,"  \"unique_24_hom_rank\":",String(RankMat(hom24[1])),",\n");
AppendTo(out,"  \"frobenius_spans_unique_24_hom\":",JsonBool(frobSpans),",\n");
AppendTo(out,"  \"socle_forced_single_24\":true,\n");
AppendTo(out,"  \"socle_forced_frobenius\":true,\n");
AppendTo(out,"  \"actual_tate_residual_image_identified\":false\n}\n");
CloseStream(out);

Print("Co1 Sym2 socle-Hom rigidity: factors=",factorDims,
  "; Hom(1,Sym2)=",hom1Dim,
  "; Hom(24,Sym2)=",hom24Dim,
  "; Hom(274,Sym2)=",hom274Dim,
  "; socle=Frobenius24 PASS\n");
QUIT;
