# Test the representation-theoretic obstruction to a nontrivial normal 2^24
# action on a characteristic-two 276-module whose Co1 composition factors are
# 1, 274, 1.
#
# Let V be the natural 24-dimensional GF(2) Co1 module.  For an elementary
# abelian normal subgroup P ~= V in P.Co1, the augmentation filtration of any
# GF(2)[P.Co1]-module M has Co1-equivariant multiplication maps
#
#   V tensor gr_i(M) -> gr_{i+1}(M).
#
# If all Hom_Co1(V tensor X,Y) vanish for X,Y in {1,274}, then P cannot act
# nontrivially on any module whose filtration factors are drawn only from
# {1,274}.  This screen computes the four required Hom spaces using the actual
# AtlasRep 24d and 274d standard-generator modules.
#
# Firewall: this does NOT prove that the actual 2B Tate head has Co1 profile
# 1,274,1.  That profile is separately tested by the Co1 wedge^2(24) and 2B
# centralizer Brauer-character screens.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
F:=GF(2);
expectedCo1Order:=4157776806543360000;

infos24:=AllAtlasGeneratingSetInfos("Co1",Dimension,24,Characteristic,2);
infos274:=AllAtlasGeneratingSetInfos("Co1",Dimension,274,Characteristic,2);
if Length(infos24)=0 or Length(infos274)=0 then
  Error("AtlasRep requires Co1 GF2 modules of dimensions 24 and 274");
fi;
G24:=AtlasGroup(infos24[1]);
G274:=AtlasGroup(infos274[1]);
if G24=fail or G274=fail then Error("failed to construct Co1 modules"); fi;
if Size(G24)<>expectedCo1Order or Size(G274)<>expectedCo1Order then
  Error("unexpected Co1 image order");
fi;

g24:=GeneratorsOfGroup(G24);
g274:=GeneratorsOfGroup(G274);
if Length(g24)<>Length(g274) then Error("standard-generator counts disagree"); fi;
if NrRows(g24[1])<>24 or NrRows(g274[1])<>274 then Error("unexpected module dimensions"); fi;

M24:=GModuleByMats(g24,F);
M274:=GModuleByMats(g274,F);
M1:=GModuleByMats(List(g24,x->ImmutableMatrix(F,[[One(F)]])),F);
T24x274:=TensorProductGModule(M24,M274);
if MTX.Dimension(T24x274)<>24*274 then Error("tensor dimension mismatch"); fi;

h24to1:=MTX.BasisModuleHomomorphisms(M24,M1);
h24to274:=MTX.BasisModuleHomomorphisms(M24,M274);
hTensorTo1:=MTX.BasisModuleHomomorphisms(T24x274,M1);
hTensorTo274:=MTX.BasisModuleHomomorphisms(T24x274,M274);

d24to1:=Length(h24to1);
d24to274:=Length(h24to274);
dTensorTo1:=Length(hTensorTo1);
dTensorTo274:=Length(hTensorTo274);
allZero:=d24to1=0 and d24to274=0 and dTensorTo1=0 and dTensorTo274=0;

JsonBool:=function(x) if x then return "true"; else return "false"; fi; end;
out:=OutputTextFile("build/co1_normal2pow24_augmentation_hom_screen.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"co1_order\":",String(expectedCo1Order),",\n");
AppendTo(out,"  \"natural_dimension\":24,\n");
AppendTo(out,"  \"large_simple_dimension\":274,\n");
AppendTo(out,"  \"tensor_dimension\":",String(MTX.Dimension(T24x274)),",\n");
AppendTo(out,"  \"hom_24_to_1_dimension\":",String(d24to1),",\n");
AppendTo(out,"  \"hom_24_to_274_dimension\":",String(d24to274),",\n");
AppendTo(out,"  \"hom_24_tensor_274_to_1_dimension\":",String(dTensorTo1),",\n");
AppendTo(out,"  \"hom_24_tensor_274_to_274_dimension\":",String(dTensorTo274),",\n");
AppendTo(out,"  \"all_augmentation_adjacent_homs_vanish\":",JsonBool(allZero),",\n");
AppendTo(out,"  \"normal_2pow24_triviality_on_any_1_274_1_filtered_module_forced\":",JsonBool(allZero),",\n");
AppendTo(out,"  \"actual_tate_has_1_274_1_profile_proved\":false,\n");
AppendTo(out,"  \"actual_tate_normal_2pow24_triviality_proved\":false\n");
AppendTo(out,"}\n");
CloseStream(out);

Print("Co1 augmentation Hom screen: 24->1=",d24to1,
  "; 24->274=",d24to274,
  "; 24x274->1=",dTensorTo1,
  "; 24x274->274=",dTensorTo274,"\n");
QUIT;
