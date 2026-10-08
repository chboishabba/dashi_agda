# Test whether the Frobenius-square 24 inside Sym^2(Co1-24) is the unique
# nonzero Co1-equivariant copy of the natural 24-dimensional GF(2) module.
#
# This sharpens the actual 2B Tate plus/minus cokernel weld.  If
# Hom_Co1(24,Sym2(24)) is one-dimensional, then any nonzero Co1-equivariant
# residual 24 -> 300 map is a scalar multiple of the explicit Frobenius-square
# embedding; over GF(2) that means it is exactly that embedding.
#
# Firewall: this does not identify the common 98280-dimensional part of the
# actual norm map.  It only removes ambiguity from the residual 24 -> 300 lane.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
F:=GF(2); n:=24;
expectedCo1Order:=4157776806543360000;

infos:=AllAtlasGeneratingSetInfos("Co1",Dimension,24,Characteristic,2);
if Length(infos)=0 then Error("Co1 24d GF2 Atlas module unavailable"); fi;
G:=AtlasGroup(infos[1]);
if G=fail or Size(G)<>expectedCo1Order then Error("failed Co1 24d module"); fi;
gens:=GeneratorsOfGroup(G);
M24:=GModuleByMats(gens,F);

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

symGens:=List(gens,SymMat);
Msym:=GModuleByMats(symGens,F);
if MTX.Dimension(Msym)<>300 then Error("Sym2 module dimension is not 300"); fi;

# Explicit Frobenius map e_i |-> e_i^2 in the ordered Sym2 basis.
frobRows:=List([1..n],i ->
  List([1..Length(symPairs)],k ->
    if symPairs[k]=[i,i] then One(F) else Zero(F) fi));
frob:=ImmutableMatrix(F,frobRows);
if RankMat(frob)<>24 then Error("explicit Frobenius map does not have rank 24"); fi;

# Verify equivariance in row-vector convention: Frobenius followed by Sym2(g)
# equals g followed by Frobenius.
for k in [1..Length(gens)] do
  if frob*symGens[k]<>gens[k]*frob then
    Error("explicit Frobenius-square map is not Co1-equivariant");
  fi;
od;

homs:=MTX.BasisModuleHomomorphisms(M24,Msym);
homDim:=Length(homs);
if homDim=0 then Error("Hom_Co1(24,Sym2(24)) unexpectedly vanishes"); fi;

# Every nonzero hom basis element should have full rank 24 if the natural
# module is irreducible.  Record ranks rather than assuming this.
homRanks:=List(homs,RankMat);
uniqueHomLine:=homDim=1;
frobSpansHom:=false;
if uniqueHomLine then
  # Over GF(2), the unique nonzero vector in a one-dimensional Hom space is the
  # basis vector itself, so equality can be checked directly.
  frobSpansHom := homs[1]=frob;
fi;

JsonBool:=function(x) if x then return "true"; else return "false"; fi; end;
PrintNatList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;

out:=OutputTextFile("build/co1_f2_frobenius24_sym2_300_hom_uniqueness_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"co1_order\":",String(Size(G)),",\n");
AppendTo(out,"  \"natural_dimension\":24,\n");
AppendTo(out,"  \"symmetric_square_dimension\":300,\n");
AppendTo(out,"  \"explicit_frobenius_rank\":",String(RankMat(frob)),",\n");
AppendTo(out,"  \"hom_24_to_sym2_dimension\":",String(homDim),",\n");
AppendTo(out,"  \"hom_basis_ranks\":"); PrintNatList(out,homRanks); AppendTo(out,",\n");
AppendTo(out,"  \"unique_nonzero_hom_line\":",JsonBool(uniqueHomLine),",\n");
AppendTo(out,"  \"explicit_frobenius_spans_hom\":",JsonBool(frobSpansHom),",\n");
AppendTo(out,"  \"actual_norm_residual_24_map_identified\":false,\n");
AppendTo(out,"  \"common_98280_map_identified\":false\n}\n");
CloseStream(out);
Print("Co1 Frobenius24->Sym2(24) Hom screen: dim=",homDim,
  "; ranks=",homRanks,"; explicit spans=",frobSpansHom,"\n");
QUIT;
