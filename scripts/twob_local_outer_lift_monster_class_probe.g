# Probe the within-fibre M22:2 outer involution through the actual constructible
# Monster-local group H = 2^(2+11+22).(M24 x S3).
#
# We lift the unique outer M22:2 class with (class size, centralizer)=(1386,640)
# from the M24 quotient.  A full lift can act nontrivially on the central 2^2,
# so we DO NOT choose an arbitrary central involution: we select a nonidentity
# central involution actually fixed by the lift.  If no such involution exists,
# this particular lift does not furnish the commuting C2xC2 test and the script
# fails honestly.
#
# CTblLib class fusions are then used fail-closed.  If the Monster labels of
# h and ah are invariant across every admissible local->Monster fusion, we also
# compute the rational V^natural_2 = 1 + 196883 character traces and the four
# C2xC2 eigenspace multiplicities.  These are inputs for an integral/mod-4
# extension test; they do NOT themselves identify the mod-2 Tate extension.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
if LoadPackage("ctbllib") <> true then Error("CTblLib is required"); fi;

localName := "2^(2+11+22).(M24xS3)";
expectedLocalOrder := 50472333605150392320;
expectedM24Order := 244823040;
expectedM22d2Order := 887040;
weightTwoDimension := 196884;

G := AtlasGroup(localName);
if G=fail or Size(G)<>expectedLocalOrder then Error("failed to construct local group"); fi;

bl1 := Blocks(G,MovedPoints(G));
hom1 := ActionHomomorphism(G,bl1,OnSets);
act1 := Image(hom1);
bl2 := Blocks(act1,MovedPoints(act1));
hom2 := ActionHomomorphism(act1,bl2,OnSets);
act2 := Image(hom2);
seeds := AllBlocks(act2);
seed3 := First(seeds,b -> Length(b)=3);
seed24 := First(seeds,b -> Length(b)=24);
orb3 := Orbit(act2,seed3,OnSets);
orb24 := Orbit(act2,seed24,OnSets);
homM24 := ActionHomomorphism(act2,orb3,OnSets);
homS3 := ActionHomomorphism(act2,orb24,OnSets);
M24q := Image(homM24); S3q := Image(homS3);
if Size(M24q)<>expectedM24Order or Size(S3q)<>6 then Error("bad quotient factors"); fi;
M24factor := Kernel(homS3);
if Size(M24factor)<>expectedM24Order then Error("kernel of S3 projection is not M24"); fi;
resM24 := RestrictedMapping(homM24,M24factor);
if Size(Image(resM24))<>expectedM24Order or Size(Kernel(resM24))<>1 then Error("M24 factor map not iso"); fi;

p276Infos := Filtered(AllAtlasGeneratingSetInfos("M24"), info ->
  IsBound(info.repname) and PositionSublist(info.repname,"p276")<>fail);
if Length(p276Infos)=0 then Error("M24 p276 unavailable"); fi;
P276 := AtlasGroup(p276Infos[1]);
H2 := Stabilizer(P276,1);
if Size(H2)<>expectedM22d2Order then Error("p276 point stabilizer not M22:2"); fi;
D22 := DerivedSubgroup(H2);
outerClasses := Filtered(ConjugacyClasses(H2),cl ->
  Order(Representative(cl))=2 and not (Representative(cl) in D22)
  and Size(cl)=1386 and Size(H2)/Size(cl)=640);
if Length(outerClasses)<>1 then Error("expected unique outer 1386/640 class"); fi;
h276 := Representative(outerClasses[1]);

isoM24 := IsomorphismGroups(P276,M24q);
if isoM24=fail then Error("cannot identify p276 M24 with local M24 quotient"); fi;
hM24q := Image(isoM24,h276);
hAct2 := PreImagesRepresentative(resM24,hM24q);
if hAct2=fail or Image(homS3,hAct2)<>One(S3q) then Error("failed pure-M24 quotient lift"); fi;
hAct1 := PreImagesRepresentative(hom2,hAct2);
hLift := PreImagesRepresentative(hom1,hAct1);
if hLift=fail then Error("failed full local lift"); fi;

O2 := PCore(G,2);
Z2 := Centre(O2);
centralInvolutions := Filtered(Elements(Z2),z -> z<>One(Z2) and Order(z)=2);
if Length(centralInvolutions)<3 then Error("local 2-core centre does not expose three involutions"); fi;
fixedCentralInvolutions := Filtered(centralInvolutions,z -> z^hLift=z);
if Length(fixedCentralInvolutions)=0 then
  Error("selected outer lift fixes no nonidentity central 2B involution");
fi;
a := fixedCentralInvolutions[1];
commutes := Comm(hLift,a)=One(G);
if not commutes then Error("fixed central involution does not commute with lift"); fi;
ah := a*hLift;

localTbl := CharacterTable(localName);
monster := CharacterTable("M");
if localTbl=fail or monster=fail then Error("required character tables unavailable"); fi;
storedFusion := GetFusionMap(localTbl,monster);
if storedFusion=fail then
  fusions := PossibleClassFusions(localTbl,monster);
  fusionSource := "PossibleClassFusions-fallback";
else
  fusions := [storedFusion];
  fusionSource := "stored-GetFusionMap";
fi;
if Length(fusions)=0 then Error("no local-to-Monster fusion available"); fi;
localOrders := OrdersClassRepresentatives(localTbl);
localCentralizers := SizesCentralizers(localTbl);
monsterNames := ClassNames(monster,"ATLAS");

ElementSignature := function(x)
  local ord,cent,cands;
  ord := Order(x);
  cent := Size(Centralizer(G,x));
  cands := Filtered([1..Length(localOrders)],i -> localOrders[i]=ord and localCentralizers[i]=cent);
  return [ord,cent,cands];
end;
sigA := ElementSignature(a);
sigH := ElementSignature(hLift);
sigAH := ElementSignature(ah);

PossibleMonsterPositions := function(sig)
  local positions,fi,ci;
  positions := [];
  for fi in [1..Length(fusions)] do
    for ci in sig[3] do AddSet(positions,fusions[fi][ci]); od;
  od;
  return positions;
end;
positionsA := PossibleMonsterPositions(sigA);
positionsH := PossibleMonsterPositions(sigH);
positionsAH := PossibleMonsterPositions(sigAH);
labelsA := List(positionsA,p -> monsterNames[p]);
labelsH := List(positionsH,p -> monsterNames[p]);
labelsAH := List(positionsAH,p -> monsterNames[p]);

# Weight-two character is 1 + the unique 196883-dimensional irreducible.
monsterIrr := Irr(monster);
chiPositions := Filtered([1..Length(monsterIrr)],i -> monsterIrr[i][1]=196883);
if Length(chiPositions)<>1 then Error("Monster table does not expose unique 196883 irrep"); fi;
chi196883 := monsterIrr[chiPositions[1]];
WeightTwoTraceAt := p -> 1 + chi196883[p];

traceA := fail; traceH := fail; traceAH := fail;
eigenspaceMultiplicities := fail;
if Length(positionsA)=1 and Length(positionsH)=1 and Length(positionsAH)=1
   and Order(a)=2 and Order(hLift)=2 and Order(ah)=2 then
  traceA := WeightTwoTraceAt(positionsA[1]);
  traceH := WeightTwoTraceAt(positionsH[1]);
  traceAH := WeightTwoTraceAt(positionsAH[1]);
  nums := [
    weightTwoDimension + traceA + traceH + traceAH,
    weightTwoDimension + traceA - traceH - traceAH,
    weightTwoDimension - traceA + traceH - traceAH,
    weightTwoDimension - traceA - traceH + traceAH
  ];
  if not ForAll(nums,n -> n mod 4 = 0) then
    Error("fusion-invariant commuting involution traces do not yield integral V4 multiplicities");
  fi;
  eigenspaceMultiplicities := List(nums,n -> n/4);
fi;

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
JsonBool := function(x) if x then return "true"; else return "false"; fi; end;
PrintSig := function(out,sig,labels)
  AppendTo(out,"{\"order\":",String(sig[1]),",\"centralizer_order\":",String(sig[2]),",\"compatible_local_table_classes\":");
  PrintNatList(out,sig[3]); AppendTo(out,",\"possible_monster_classes\":"); PrintStringList(out,labels); AppendTo(out,"}");
end;
PrintMaybeInt := function(out,x)
  if x=fail then AppendTo(out,"null"); else AppendTo(out,String(x)); fi;
end;
PrintMaybeNatList := function(out,x)
  if x=fail then AppendTo(out,"null"); else PrintNatList(out,x); fi;
end;

out := OutputTextFile("build/twob_local_outer_lift_monster_class_probe.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"local_group_order\":",String(Size(G)),",\n");
AppendTo(out,"  \"o2_order\":",String(Size(O2)),",\n");
AppendTo(out,"  \"o2_centre_order\":",String(Size(Z2)),",\n");
AppendTo(out,"  \"central_involution_count\":",String(Length(centralInvolutions)),",\n");
AppendTo(out,"  \"fixed_central_involution_count\":",String(Length(fixedCentralInvolutions)),",\n");
AppendTo(out,"  \"outer_quotient_class_size\":1386,\n");
AppendTo(out,"  \"outer_quotient_centralizer_order\":640,\n");
AppendTo(out,"  \"full_lift_order\":",String(Order(hLift)),",\n");
AppendTo(out,"  \"product_order\":",String(Order(ah)),",\n");
AppendTo(out,"  \"lift_commutes_with_selected_central_2B\":",JsonBool(commutes),",\n");
AppendTo(out,"  \"fusion_source\":\"",fusionSource,"\",\n");
AppendTo(out,"  \"possible_fusion_count\":",String(Length(fusions)),",\n");
AppendTo(out,"  \"a_signature\":"); PrintSig(out,sigA,labelsA); AppendTo(out,",\n");
AppendTo(out,"  \"h_signature\":"); PrintSig(out,sigH,labelsH); AppendTo(out,",\n");
AppendTo(out,"  \"ah_signature\":"); PrintSig(out,sigAH,labelsAH); AppendTo(out,",\n");
AppendTo(out,"  \"a_monster_class_fusion_invariant\":",JsonBool(Length(labelsA)=1),",\n");
AppendTo(out,"  \"h_monster_class_fusion_invariant\":",JsonBool(Length(labelsH)=1),",\n");
AppendTo(out,"  \"ah_monster_class_fusion_invariant\":",JsonBool(Length(labelsAH)=1),",\n");
AppendTo(out,"  \"weight_two_trace_a\":"); PrintMaybeInt(out,traceA); AppendTo(out,",\n");
AppendTo(out,"  \"weight_two_trace_h\":"); PrintMaybeInt(out,traceH); AppendTo(out,",\n");
AppendTo(out,"  \"weight_two_trace_ah\":"); PrintMaybeInt(out,traceAH); AppendTo(out,",\n");
AppendTo(out,"  \"v4_rational_eigenspace_multiplicities\":"); PrintMaybeNatList(out,eigenspaceMultiplicities); AppendTo(out,"\n}\n");
CloseStream(out);
Print("2B local outer-lift Monster class probe: lift order=",Order(hLift),
  "; product order=",Order(ah),"; fixed central 2B count=",Length(fixedCentralInvolutions),
  "; fusion=",fusionSource,"; H labels=",labelsH,"; aH labels=",labelsAH,"\n");
QUIT;
