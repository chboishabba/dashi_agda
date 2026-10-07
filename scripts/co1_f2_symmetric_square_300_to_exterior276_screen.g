# Construct the actual Atlas Co1 24-dimensional GF(2) module and verify the
# characteristic-two exact sequence
#
#   0 -> Frobenius-square 24 -> Sym^2(24) -> wedge^2(24) -> 0.
#
# The 300-dimensional symmetric square is built on monomials x_i x_j, i<=j.
# In characteristic two, the 24 square monomials x_i^2 form an invariant
# subspace.  Modulo that square subspace, the induced 276-dimensional action on
# off-diagonal monomials is exactly the exterior-square action.
#
# This is a concrete Co1 module-theoretic realization of 300 = 24 + 276.  It is
# highly relevant to the 2B centralizer decomposition 98304+98280+300, but this
# script does NOT identify the resulting 276 quotient with the actual Tate head.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
F:=GF(2); n:=24;
infos:=AllAtlasGeneratingSetInfos("Co1",Dimension,24,Characteristic,2);
if Length(infos)=0 then Error("Co1 24d GF2 Atlas module unavailable"); fi;
G:=AtlasGroup(infos[1]);
if G=fail or Size(G)<>4157776806543360000 then Error("failed Co1 24d module"); fi;
gens:=GeneratorsOfGroup(G);

symPairs:=[]; offPairs:=[];
for i in [1..n] do
  for j in [i..n] do Add(symPairs,[i,j]); if i<j then Add(offPairs,[i,j]); fi; od;
od;
if Length(symPairs)<>300 or Length(offPairs)<>276 then Error("bad symmetric/exterior dimensions"); fi;

SymMat:=function(A)
  local rows,ij,pq,row,i,j,p,q,c;
  rows:=[];
  for ij in symPairs do
    i:=ij[1]; j:=ij[2]; row:=[];
    for pq in symPairs do
      p:=pq[1]; q:=pq[2];
      if p=q then c:=A[i][p]*A[j][p];
      else c:=A[i][p]*A[j][q] + A[i][q]*A[j][p]; fi;
      Add(row,c);
    od;
    Add(rows,row);
  od;
  return ImmutableMatrix(F,rows);
end;

ExtMat:=function(A)
  local rows,ij,pq,row,i,j,p,q,c;
  rows:=[];
  for ij in offPairs do
    i:=ij[1]; j:=ij[2]; row:=[];
    for pq in offPairs do
      p:=pq[1]; q:=pq[2];
      c:=A[i][p]*A[j][q] + A[i][q]*A[j][p];
      Add(row,c);
    od;
    Add(rows,row);
  od;
  return ImmutableMatrix(F,rows);
end;

symGens:=List(gens,SymMat);
extGens:=List(gens,ExtMat);

# Indices of square and off-diagonal basis vectors in the 300 basis.
squareIdx:=Filtered([1..300],k -> symPairs[k][1]=symPairs[k][2]);
offIdx:=Filtered([1..300],k -> symPairs[k][1]<>symPairs[k][2]);
if Length(squareIdx)<>24 or Length(offIdx)<>276 then Error("bad block index counts"); fi;

squareStable:=true;
quotientMatchesExterior:=true;
for gi in [1..Length(symGens)] do
  S:=symGens[gi]; E:=extGens[gi];
  # Square input rows must have zero coefficients on off-diagonal outputs.
  for i in squareIdx do for j in offIdx do if S[i][j]<>Zero(F) then squareStable:=false; fi; od; od;
  # Quotient block on off-diagonal basis equals the exterior-square matrix.
  Q:=S{offIdx}{offIdx};
  if Q<>E then quotientMatchesExterior:=false; fi;
od;
if not squareStable then Error("Frobenius-square 24 is not stable"); fi;
if not quotientMatchesExterior then Error("Sym2/squares quotient is not exterior square"); fi;

Msym:=GModuleByMats(symGens,F);
Mext:=GModuleByMats(extGens,F);
symFactors:=MTX.CompositionFactors(Msym);
extFactors:=MTX.CompositionFactors(Mext);
symSeries:=MTX.BasesCompositionSeries(Msym);
extSeries:=MTX.BasesCompositionSeries(Mext);

PrintNatList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;

out:=OutputTextFile("build/co1_f2_symmetric_square_300_to_exterior276_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"co1_order\":",String(Size(G)),",\n");
AppendTo(out,"  \"natural_dimension\":24,\n");
AppendTo(out,"  \"symmetric_square_dimension\":300,\n");
AppendTo(out,"  \"frobenius_square_submodule_dimension\":24,\n");
AppendTo(out,"  \"quotient_dimension\":276,\n");
AppendTo(out,"  \"square_subspace_stable\":true,\n");
AppendTo(out,"  \"quotient_matrices_equal_exterior_square\":true,\n");
AppendTo(out,"  \"sym2_composition_factor_dimensions\":"); PrintNatList(out,List(symFactors,f->MTX.Dimension(f))); AppendTo(out,",\n");
AppendTo(out,"  \"exterior_composition_factor_dimensions\":"); PrintNatList(out,List(extFactors,f->MTX.Dimension(f))); AppendTo(out,",\n");
AppendTo(out,"  \"sym2_series_dimensions\":"); PrintNatList(out,List(symSeries,Length)); AppendTo(out,",\n");
AppendTo(out,"  \"exterior_series_dimensions\":"); PrintNatList(out,List(extSeries,Length)); AppendTo(out,",\n");
AppendTo(out,"  \"actual_2b_tate_identified_with_quotient\":false\n}\n");
CloseStream(out);
Print("Co1 Sym2 exact-sequence screen: Sym2 factors=",List(symFactors,f->MTX.Dimension(f)),
  "; wedge factors=",List(extFactors,f->MTX.Dimension(f)),"\n");
QUIT;
