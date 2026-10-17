# Test whether the Frobenius-square 24-dimensional submodule of
# Sym^2(Co1-24) is the unique 24-dimensional minimal Co1-submodule.
#
# If PASS, then any actual residual norm image that is known independently to
# be a 24-dimensional simple Co1-submodule of Sym^2(24) must equal the
# Frobenius-square image as a literal submodule.  This bypasses a separate
# quotient-chart/Hom-line identification.
#
# Firewall: this screen says nothing about the actual Tate residual image until
# that image is proved 24-dimensional, Co1-stable and simple/natural.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
F := GF(2); n := 24;
expectedCo1Order := 4157776806543360000;

infos := AllAtlasGeneratingSetInfos("Co1",Dimension,24,Characteristic,2);
if Length(infos)=0 then Error("Co1 24d GF2 Atlas module unavailable"); fi;
G := AtlasGroup(infos[1]);
if G=fail or Size(G)<>expectedCo1Order then Error("failed Co1 24d module"); fi;
gens := GeneratorsOfGroup(G);

symPairs := [];
for i in [1..n] do for j in [i..n] do Add(symPairs,[i,j]); od; od;
if Length(symPairs)<>300 then Error("Sym2 basis size is not 300"); fi;

SymMat := function(A)
  local rows,ij,pq,row,i,j,p,q,c;
  rows := [];
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

symGens := List(gens,SymMat);
Msym := GModuleByMats(symGens,F);
if MTX.Dimension(Msym)<>300 then Error("Sym2 module dimension is not 300"); fi;

# Explicit Frobenius image basis e_i |-> e_i^2.
frobRows := List([1..n],i ->
  List([1..Length(symPairs)],k ->
    if symPairs[k]=[i,i] then One(F) else Zero(F) fi));
if RankMat(frobRows)<>24 then Error("explicit Frobenius basis rank is not 24"); fi;

# Minimal submodules and socle are substantially cheaper than enumerating the
# complete submodule lattice of the 300-dimensional module.
minimalBases := MTX.BasesMinimalSubmodules(Msym);
minimalDims := List(minimalBases,Length);
socleBasis := MTX.BasisSocle(Msym);
socleDim := Length(socleBasis);

bases24 := Filtered(minimalBases,b -> Length(b)=24);
uniqueMinimal24 := Length(bases24)=1;
frobEqualsUnique24 := false;
if uniqueMinimal24 then
  b24 := bases24[1];
  # Row spaces are equal iff concatenating the two full-rank 24-row bases does
  # not increase rank.
  frobEqualsUnique24 := RankMat(Concatenation(b24,frobRows))=24;
fi;

socleEqualsFrob := false;
if socleDim=24 then
  socleEqualsFrob := RankMat(Concatenation(socleBasis,frobRows))=24;
fi;

JsonBool := function(x) if x then return "true"; else return "false"; fi; end;
PrintNatList := function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do
    if i>1 then AppendTo(out,","); fi;
    AppendTo(out,String(xs[i]));
  od;
  AppendTo(out,"]");
end;

out := OutputTextFile("build/co1_f2_sym2_unique_minimal24_submodule_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"co1_order\":",String(Size(G)),",\n");
AppendTo(out,"  \"symmetric_square_dimension\":300,\n");
AppendTo(out,"  \"minimal_submodule_dimensions\":"); PrintNatList(out,minimalDims); AppendTo(out,",\n");
AppendTo(out,"  \"minimal_submodule_count\":",String(Length(minimalBases)),",\n");
AppendTo(out,"  \"minimal_24_submodule_count\":",String(Length(bases24)),",\n");
AppendTo(out,"  \"unique_minimal_24_submodule\":",JsonBool(uniqueMinimal24),",\n");
AppendTo(out,"  \"unique_minimal_24_equals_frobenius\":",JsonBool(frobEqualsUnique24),",\n");
AppendTo(out,"  \"socle_dimension\":",String(socleDim),",\n");
AppendTo(out,"  \"socle_equals_frobenius\":",JsonBool(socleEqualsFrob),",\n");
AppendTo(out,"  \"actual_tate_residual_image_identified\":false\n}\n");
CloseStream(out);

Print("Co1 Sym2 minimal-submodule screen: minimal dims=",minimalDims,
  "; minimal24 count=",Length(bases24),"; socle dim=",socleDim,
  "; unique24=frob? ",frobEqualsUnique24,"; socle=frob? ",socleEqualsFrob,"\n");
QUIT;
