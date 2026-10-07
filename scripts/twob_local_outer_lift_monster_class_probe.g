# Probe the within-fibre M22:2 outer involution through the actual constructible
# Monster-local group H = 2^(2+11+22).(M24 x S3).
#
# Goal:
#   1. construct the quotient M24 x S3 as in the existing local-group receipt;
#   2. construct the M24 p276 stabilizer H2=M22:2 and select its outer class
#      of size 1386 / centralizer 640;
#   3. transport that element into the pure M24 factor of the local quotient;
#   4. lift it to the full local group;
#   5. extract the central 2^2 of the local 2-core (the sourced 2B-pure V4);
#   6. test whether the chosen lift centralizes a selected central involution a;
#   7. inspect all CTblLib-possible local->Monster class fusions and report the
#      possible Monster class labels for local table classes compatible with
#      the observed orders/centralizer data.
#
# This is deliberately a probe.  A lift in a non-split 2-local extension can
# depend on kernel choices, so no Monster class is promoted unless all admissible
# fusions and all checked lift invariants agree.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
if LoadPackage("ctbllib") <> true then Error("CTblLib is required"); fi;

localName := "2^(2+11+22).(M24xS3)";
expectedLocalOrder := 50472333605150392320;
expectedM24Order := 244823040;
expectedM22d2Order := 887040;

G := AtlasGroup(localName);
if G=fail or Size(G)<>expectedLocalOrder then Error("failed to construct local group"); fi;

# Existing two-stage block quotient to M24 x S3.
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
homM24 := ActionHomomorphism(act2,orb3,OnSets);  # 24 blocks -> M24
homS3 := ActionHomomorphism(act2,orb24,OnSets);  # 3 blocks -> S3
M24q := Image(homM24);
S3q := Image(homS3);
if Size(M24q)<>expectedM24Order or Size(S3q)<>6 then Error("bad quotient factors"); fi;
M24factor := Kernel(homS3);
if Size(M24factor)<>expectedM24Order then Error("kernel of S3 projection is not M24"); fi;
resM24 := RestrictedMapping(homM24,M24factor);
if Size(Image(resM24))<>expectedM24Order or Size(Kernel(resM24))<>1 then Error("M24 factor map not iso"); fi;

# Source p276 model and outer M22:2 class.
p276Infos := Filtered(AllAtlasGeneratingSetInfos("M24"), info ->
  IsBound(info.repname) and PositionSublist(info.repname,"p276")<>fail);
if Length(p276Infos)=0 then Error("M24 p276 unavailable"); fi;
P276 := AtlasGroup(p276Infos[1]);
H2 := Stabilizer(P276,1);
if Size(H2)<>expectedM22d2Order then Error("p276 point stabilizer not M22:2"); fi;
D22 := DerivedSubgroup(H2);
outerClasses := Filtered(ConjugacyClasses(H2),cl ->
  Order(Representative(cl))=2
  and not (Representative(cl) in D22)
  and Size(cl)=1386
  and Size(H2)/Size(cl)=640);
if Length(outerClasses)<>1 then Error("expected unique outer 1386/640 class"); fi;
h276 := Representative(outerClasses[1]);

isoM24 := IsomorphismGroups(P276,M24q);
if isoM24=fail then Error("cannot identify p276 M24 with local M24 quotient"); fi;
hM24q := Image(isoM24,h276);
hAct2 := PreImagesRepresentative(resM24,hM24q);
if hAct2=fail or Image(homS3,hAct2)<>One(S3q) then Error("failed pure-M24 quotient lift"); fi;

# Lift through the two block homomorphisms.  Record rather than assume the order.
hAct1 := PreImagesRepresentative(hom2,hAct2);
hLift := PreImagesRepresentative(hom1,hAct1);
if hLift=fail then Error("failed full local lift"); fi;

# The normal 2-core should expose the central 2^2 pure Klein four.
O2 := PCore(G,2);
Z2 := Centre(O2);
centralInvolutions := Filtered(Elements(Z2),z -> z<>One(Z2) and Order(z)=2);
if Length(centralInvolutions)<3 then Error("local 2-core centre does not expose three involutions"); fi;
a := centralInvolutions[1];
commutes := Comm(hLift,a)=One(G);
ah := a*hLift;

# CTblLib table and all currently admissible Monster fusions.
localTbl := CharacterTable(localName);
monster := CharacterTable("M");
if localTbl=fail or monster=fail then Error("required character tables unavailable"); fi;
fusions := PossibleClassFusions(localTbl,monster);
if Length(fusions)=0 then Error("no admissible local-to-Monster fusions"); fi;
localOrders := OrdersClassRepresentatives(localTbl);
localCentralizers := SizesCentralizers(localTbl);
monsterNames := ClassNames(monster,"ATLAS");

# We do not pretend to have an automatic conjugacy-class identification from
# the constructed permutation group to the library table.  Instead retain the
# exact group invariants we can compute and list all table classes compatible
# with those invariants.  Centralizer calculations are attempted only for the
# three specific elements.
ElementSignature := function(x)
  local ord,cent,cands;
  ord := Order(x);
  cent := Size(Centralizer(G,x));
  cands := Filtered([1..Length(localOrders)],i ->
    localOrders[i]=ord and localCentralizers[i]=cent);
  return [ord,cent,cands];
end;

sigA := ElementSignature(a);
sigH := ElementSignature(hLift);
sigAH := ElementSignature(ah);

PossibleMonsterLabels := function(sig)
  local labels,fi,ci;
  labels := [];
  for fi in [1..Length(fusions)] do
    for ci in sig[3] do AddSet(labels,monsterNames[fusions[fi][ci]]); od;
  od;
  return labels;
end;

labelsA := PossibleMonsterLabels(sigA);
labelsH := PossibleMonsterLabels(sigH);
labelsAH := PossibleMonsterLabels(sigAH);

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

out := OutputTextFile("build/twob_local_outer_lift_monster_class_probe.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"local_group_order\":",String(Size(G)),",\n");
AppendTo(out,"  \"o2_order\":",String(Size(O2)),",\n");
AppendTo(out,"  \"o2_centre_order\":",String(Size(Z2)),",\n");
AppendTo(out,"  \"central_involution_count\":",String(Length(centralInvolutions)),",\n");
AppendTo(out,"  \"outer_quotient_class_size\":1386,\n");
AppendTo(out,"  \"outer_quotient_centralizer_order\":640,\n");
AppendTo(out,"  \"full_lift_order\":",String(Order(hLift)),",\n");
AppendTo(out,"  \"lift_commutes_with_selected_central_2B\":",JsonBool(commutes),",\n");
AppendTo(out,"  \"possible_fusion_count\":",String(Length(fusions)),",\n");
AppendTo(out,"  \"a_signature\":"); PrintSig(out,sigA,labelsA); AppendTo(out,",\n");
AppendTo(out,"  \"h_signature\":"); PrintSig(out,sigH,labelsH); AppendTo(out,",\n");
AppendTo(out,"  \"ah_signature\":"); PrintSig(out,sigAH,labelsAH); AppendTo(out,",\n");
AppendTo(out,"  \"h_monster_class_fusion_invariant\":",JsonBool(Length(labelsH)=1),",\n");
AppendTo(out,"  \"ah_monster_class_fusion_invariant\":",JsonBool(Length(labelsAH)=1),"\n}\n");
CloseStream(out);
Print("2B local outer-lift Monster class probe written: lift order=",Order(hLift),
  "; commute=",commutes,"; possible fusions=",Length(fusions),"; H labels=",labelsH,"; aH labels=",labelsAH,"\n");
QUIT;
