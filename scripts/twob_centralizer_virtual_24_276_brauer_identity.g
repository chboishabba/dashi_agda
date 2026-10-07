# Test the structural odd-class identity behind the 2B Tate-276 Brauer match.
#
# Weight-two restriction to the 2B centralizer has sourced dimensions
#   98304 + 98280 + 300 = 196884.
# The 300 factor is 1+299 from Co1.  We construct the actual Atlas Co1 24d
# GF(2) module and its exterior-square 276, compute their Brauer character
# values on all 2-regular Co1 classes, and test candidate centralizer character
# pairs for
#
#   chi_98304 - chi_98280 = phi_24,
#   chi_98280 + (1+chi_299) - chi_98304 = phi_wedge2_24.
#
# This is a character-level identity only.  It does not prove the integral
# norm-image exact sequence needed for the literal Tate same-object weld.

if LoadPackage("atlasrep") <> true then Error("AtlasRep is required"); fi;
if LoadPackage("ctbllib") <> true then Error("CTblLib is required"); fi;
F:=GF(2);

co1:=CharacterTable("Co1");
cent:=CharacterTable("2^1+24.Co1");
if co1=fail or cent=fail then Error("required character tables unavailable"); fi;
fus:=GetFusionMap(cent,co1);
if fus=fail then Error("stored 2B-centralizer -> Co1 fusion unavailable"); fi;

infos:=AllAtlasGeneratingSetInfos("Co1",Dimension,24,Characteristic,2);
if Length(infos)=0 then Error("Co1 24d GF2 Atlas module unavailable"); fi;
G24:=AtlasGroup(infos[1]);
if G24=fail then Error("failed to construct Co1 24d GF2 module"); fi;
tblG:=CharacterTable(G24);
tr:=TransformingPermutationsCharacterTables(tblG,co1);
if tr=fail then Error("could not align constructed Co1 table with CTblLib Co1"); fi;
classesG:=ConjugacyClasses(G24);
phi24G:=List(classesG,cl -> BrauerCharacterValue(Representative(cl)));
phi24:=Permuted(phi24G,tr.columns);
if ForAny([1..Length(phi24)],i -> OrdersClassRepresentatives(co1)[i] mod 2=1 and phi24[i]=fail) then
  Error("failed to compute a 24d Brauer value on an odd class");
fi;

# Exterior-square Brauer values via the standard character formula on odd
# classes: (phi(g)^2 - phi(g^2))/2.  Use the Co1 square power map.
pow2:=PowerMap(co1,2);
phi276:=[];
for i in [1..Length(phi24)] do
  if OrdersClassRepresentatives(co1)[i] mod 2=1 then
    Add(phi276,(phi24[i]^2-phi24[pow2[i]])/2);
  else
    Add(phi276,fail);
  fi;
od;

irrCent:=Irr(cent);
degCent:=List(irrCent,chi->chi[1]);
pos98280:=Positions(degCent,98280);
pos98304:=Positions(degCent,98304);
if Length(pos98280)=0 or Length(pos98304)=0 then Error("centralizer 98280/98304 chars unavailable"); fi;

irrCo1:=Irr(co1);
pos299:=Positions(List(irrCo1,x->x[1]),299);
if Length(pos299)=0 then Error("Co1 299 ordinary character unavailable"); fi;
chi300Co1:=irrCo1[1]+irrCo1[pos299[1]];

ordersCent:=OrdersClassRepresentatives(cent);
oddCent:=Filtered([1..Length(ordersCent)],i->ordersCent[i] mod 2=1);

passing:=[];
for i982 in pos98280 do
  for i983 in pos98304 do
    chi982:=irrCent[i982]; chi983:=irrCent[i983];
    ok24:=ForAll(oddCent,i -> chi983[i]-chi982[i]=phi24[fus[i]]);
    ok276:=ForAll(oddCent,i -> chi982[i]+chi300Co1[fus[i]]-chi983[i]=phi276[fus[i]]);
    if ok24 and ok276 then Add(passing,[i982,i983]); fi;
  od;
od;

PrintNatList:=function(out,xs)
  local i; AppendTo(out,"[");
  for i in [1..Length(xs)] do if i>1 then AppendTo(out,","); fi; AppendTo(out,String(xs[i])); od;
  AppendTo(out,"]");
end;
PrintPairList:=function(out,xss)
  local i; AppendTo(out,"[");
  for i in [1..Length(xss)] do if i>1 then AppendTo(out,","); fi; PrintNatList(out,xss[i]); od;
  AppendTo(out,"]");
end;

out:=OutputTextFile("build/twob_centralizer_virtual_24_276_brauer_identity.json",false);
SetPrintFormattingStatus(out,false);
AppendTo(out,"{\n");
AppendTo(out,"  \"centralizer_order\":",String(Size(cent)),",\n");
AppendTo(out,"  \"co1_order\":",String(Size(co1)),",\n");
AppendTo(out,"  \"odd_centralizer_class_count\":",String(Length(oddCent)),",\n");
AppendTo(out,"  \"degree_98280_character_positions\":"); PrintNatList(out,pos98280); AppendTo(out,",\n");
AppendTo(out,"  \"degree_98304_character_positions\":"); PrintNatList(out,pos98304); AppendTo(out,",\n");
AppendTo(out,"  \"passing_character_pairs\":"); PrintPairList(out,passing); AppendTo(out,",\n");
AppendTo(out,"  \"passing_pair_count\":",String(Length(passing)),",\n");
AppendTo(out,"  \"virtual_24_identity_has_solution\":",String(Length(passing)>0),",\n");
AppendTo(out,"  \"virtual_276_identity_has_same_solution\":",String(Length(passing)>0),",\n");
AppendTo(out,"  \"integral_norm_exact_sequence_paid\":false\n}\n");
CloseStream(out);
Print("2B centralizer virtual identity screen: 98280 chars=",pos98280,"; 98304 chars=",pos98304,"; passing=",passing,"\n");
QUIT;
