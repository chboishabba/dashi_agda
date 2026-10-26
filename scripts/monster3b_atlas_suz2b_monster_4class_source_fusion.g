# Source-selected Monster 3B rotation 4-class fusion, from PRE-EXISTING CTblLib maps.
#
# ORIGINAL AUTHORITY / SOURCE ROOTS:
# ATLAS of Finite Group Representations Suzuki/Monster class data.
# R.W. Barraclough & R.A. Wilson, LMS J Comput Math 10 (2007),
# DOI 10.1112/S1461157000001352, and their original N3BetcTables
# supplementary class and quotient maps https://www.rwb.me.uk/table/
# Breuer--Magaard--Wilson (2026) original table/selected diagonal sources.
# CTblLib catalog explicitly stores 6.Suz.2 -> 2.Suz.2, Suz.2,
# and 6.Suz.2 -> 3^1+12:6.Suz.2 fusions, all independent of the
# earlier finite AtlasRep 12D module coordinate chart.
#
# PRIOR REPO OWNERS:
# PR #1098: SHA256 original ATLAS 12D 2.Suz:2 C,D words; source r
# has order4, r^2=-I, m conjugates r to inverse, and an explicit
# order7 element commutes with r, selecting its SUZ quotient class 2B.
# PR #1250: all-conductor 6.Suz 78 family selection, original
# main->MN3B->Monster quotient and phase gates.
#
# GOAL: compute a genuine SOURCE-TABLE candidate Monster 4-class
# via exact fusion maps WITHOUT guessing a particular 2.Suz:2 class.
# Every 2.Suz:2 class with order4, square central -I, projecting
# to Suz involution 2B is explored. Every 6.Suz:2 order4 class
# above it must map through the published split main table.
# If the output is not UNIQUE among Monster 4A/4C/4D, return
# AMBIGUOUS and do not claim a source-selected class. This is
# SOURCE-WRITTEN; no GAP execution receipt as of the commit.
#
# NO PossibleClassFusions, character-degree numerology, or guessed
# Monster 4A/C/D labels is accepted here.

if LoadPackage("ctbllib") <> true then
  Error("CTblLib required; primary source not available");
fi;

suz := CharacterTable("Suz");
suzOuter := CharacterTable("Suz.2");
two := CharacterTable("2.Suz.2");
six := CharacterTable("6.Suz.2");
main := CharacterTable("3^1+12:6.Suz.2");
mn := CharacterTable("MN3B");
if mn = fail then mn := CharacterTable("3^1+12.2.Suz.2"); fi;
mon := CharacterTable("M");
if ForAny([suz,suzOuter,two,six,main,mn,mon],x->x=fail) then
  Error("missing exact original Suzuki/main/MN3B/Monster source table");
fi;

ExactStoredFusion := function(source,target,label)
  local f;
  f:=GetFusionMap(source,target);
  if f=fail then
    Error(Concatenation("MISSING exact stored fusion: ",label));
  fi;
  if Length(f) <> Length(OrdersClassRepresentatives(source)) or
     ForAny(f,x->not IsInt(x) or x<1 or
                    x>Length(OrdersClassRepresentatives(target))) then
    Error(Concatenation("INVALID exact stored fusion: ",label));
  fi;
  return f;
end;

# Source quotient/subgroup map directions are essential:
# Suz -> Suz.2          subgroup
# 2.Suz.2 -> Suz.2      central C2 quotient
# 6.Suz.2 -> 2.Suz.2    central C3 quotient
# 6.Suz.2 -> main       SPLIT SUBGROUP, not a quotient
# main -> 6.Suz.2       extraspecial E quotient
# main -> MN3B          original DIAGONAL C3 quotient
# MN3B -> Monster       original Monster subgroup fusion
suzToOuter:=ExactStoredFusion(suz,suzOuter,"Suz -> Suz.2");
twoToOuter:=ExactStoredFusion(two,suzOuter,"2.Suz.2 -> Suz.2");
sixToTwo:=ExactStoredFusion(six,two,"6.Suz.2 -> 2.Suz.2");
sixToMain:=ExactStoredFusion(six,main,"6.Suz.2 -> main");
mainToSix:=ExactStoredFusion(main,six,"main -> 6.Suz.2");
mainToMN:=ExactStoredFusion(main,mn,"main -> MN3B");
mnToMonster:=ExactStoredFusion(mn,mon,"MN3B -> M");

if ForAny([1..Length(sixToMain)],
          i->mainToSix[sixToMain[i]]<>i) then
  Error("source SIX -> MAIN subgroup and MAIN -> SIX quotient do not commute");
fi;

suzOrders:=OrdersClassRepresentatives(suz);
suzSizes:=SizesConjugacyClasses(suz);
suz2B:=Filtered([1..Length(suzOrders)],i->
  suzOrders[i]=2 and Size(suz)/suzSizes[i]=161280);
if Length(suz2B)<>1 then
  Error("original ATLAS Suz quotient 2B involution not unique");
fi;
suz2BPos:=suz2B[1];
if Size(suz)/suzSizes[suz2BPos]<>161280 or
   3317760 mod 7=0 or 161280 mod 7<>0 then
  Error("Suzuki original involution class centralizer source inconsistent");
fi;
suzOuterClass:=suzToOuter[suz2BPos];
if OrdersClassRepresentatives(suzOuter)[suzOuterClass]<>2 then
  Error("Suz 2B -> Suz.2 image has wrong order");
fi;

twoOrders:=OrdersClassRepresentatives(two);
twoCentralPositions:=ClassPositionsOfCentre(two);
twoCentralMinusOne:=Filtered(twoCentralPositions,i->twoOrders[i]=2);
if Length(twoCentralMinusOne)<>1 then
  Error("original 2.Suz.2 central -I involution ambiguous");
fi;
twoNegOne:=twoCentralMinusOne[1];
twoPow2:=PowerMap(two,2);
sixOrders:=OrdersClassRepresentatives(six);
sixPow2:=PowerMap(six,2);
monOrders:=OrdersClassRepresentatives(mon);
monSizes:=SizesConjugacyClasses(mon);
monPow2:=PowerMap(mon,2);
degree196883:=Filtered(Irr(mon),chi->chi[1]=196883);
if Length(degree196883)<>1 then
  Error("Monster degree196883 ordinary character not unique");
fi;
chi:=degree196883[1];
monster2B:=Filtered([1..Length(monOrders)],i->
  monOrders[i]=2 and chi[i]=275);
if Length(monster2B)<>1 then
  Error("ordinary Monster involution class 2B not unique");
fi;
monster2BPos:=monster2B[1];

MonsterFourLabelByCentralizer := function(pos)
  local ct;
  ct:=Size(mon)/monSizes[pos];
  if ct=8317584273309696000 then return "4A"; fi;
  if ct=48704929136640 then return "4C"; fi;
  if ct=8244323942400 then return "4D"; fi;
  return fail;
end;

sourceCandidates:=Filtered([1..Length(twoOrders)],i->
  twoOrders[i]=4 and twoPow2[i]=twoNegOne and
  twoToOuter[i]=suzOuterClass);
if Length(sourceCandidates)=0 then
  Error("NO source 2.Suz.2 class has order4, square -I and Suz 2B image");
fi;

liftRows:=[];
for twoPos in sourceCandidates do
  # A C3 central cover of an element of order4 has a UNIQUE
  # order4 lift at element level; check uniqueness at CLASS level.
  sixPositions:=Filtered([1..Length(sixOrders)],j->
    sixOrders[j]=4 and sixToTwo[j]=twoPos and
    sixToTwo[sixPow2[j]]=twoNegOne);
  if Length(sixPositions)<>1 then
    Error("source 2.Suz.2 class does not have unique order4 lift in 6.Suz.2");
  fi;
  sixPos:=sixPositions[1];
  mainPos:=sixToMain[sixPos];
  mnPos:=mainToMN[mainPos];
  monPos:=mnToMonster[mnPos];
  if monOrders[monPos]<>4 or monPow2[monPos]<>monster2BPos then
    Error("source class order4/square2B failed the actual Monster fusion");
  fi;
  lbl:=MonsterFourLabelByCentralizer(monPos);
  if lbl=fail then
    Error("actual Monster 4-class centralizer outside sourced 4A/4C/4D");
  fi;
  Add(liftRows,rec(twoPos:=twoPos,sixPos:=sixPos,
                   mainPos:=mainPos,mnPos:=mnPos,
                   monsterPos:=monPos,monsterLabel:=lbl));
od;

possibleMonsterLabels:=Set(List(liftRows,row->row.monsterLabel));
if Length(possibleMonsterLabels)=0 then
  Error("no admissible exact Monster source class");
fi;
isUnique:=Length(possibleMonsterLabels)=1;

# Return the actual SELECTED CLASS only if every possible source
# class maps to the same Monster class. Otherwise write AMBIGUOUS
# WITH THE ORIGINAL CLASS POSITIONS intact, for further matrix/group
# word discrimination. In particular, do not confuse the image of r
# (Suz class 2B involution) with its source Monster class (order4).
outPath:="build/monster3b_atlas_suz2b_monster_4class_source_fusion.json";
PrintTo(outPath,
  "{\n",
  "  \"schema\": \"monster3b-atlas-source-Suz2B-to-Monster4-fusion-v1\",\n",
  "  \"original_source\": \"ATLAS, Barraclough-Wilson 2007 and CTblLib stored maps\",\n",
  "  \"source_suz_2b_position\": ",suz2BPos,",\n",
  "  \"source_suz_outer_position\": ",suzOuterClass,",\n",
  "  \"source_two_suz_central_minus_one_position\": ",twoNegOne,",\n",
  "  \"actual_monster_twoB_position\": ",monster2BPos,",\n",
  "  \"source_two_suz_order4_candidates_count\": ",Length(sourceCandidates),",\n",
  "  \"candidates\": [\n");
for i in [1..Length(liftRows)] do
  row:=liftRows[i];
  AppendTo(outPath,
    "    {\"two_suz_class_position\":",row.twoPos,
    ",\"six_suz_class_position\":",row.sixPos,
    ",\"main_class_position\":",row.mainPos,
    ",\"mn3b_class_position\":",row.mnPos,
    ",\"monster_class_position\":",row.monsterPos,
    ",\"monster_four_label\":\"",row.monsterLabel,"\"}",
    (if i<Length(liftRows) then ",\n" else "\n" fi));
od;
AppendTo(outPath,
  "  ],\n",
  "  \"all_possible_monster_four_labels\": [");
for i in [1..Length(possibleMonsterLabels)] do
  AppendTo(outPath,"\"",possibleMonsterLabels[i],"\"",
    (if i<Length(possibleMonsterLabels) then "," else "" fi));
od;
AppendTo(outPath,
  "],\n",
  "  \"literal_source_word_2Suz_class_individually_identified\": false,\n",
  "  \"actual_6Suz_degree78_family_selected\": false,\n",
  "  \"full_actual_Monster_Hom_constructed\": false,\n",
  "  \"actual_monster_four_class_uniquely_forced_by_class_fusions\": ",
  (if isUnique then "true" else "false" fi),",\n",
  "  \"status\": \"",
  (if isUnique then "UNIQUE_SOURCE_FUSION" else "AMBIGUOUS_SOURCE_FUSION" fi),
  "\"\n}\n");

Print("SOURCE MONSTER-4-CLASS FUSION: ",
      (if isUnique then "UNIQUE " else "AMBIGUOUS " fi),
      possibleMonsterLabels,
      "; candidate twoSuz classes=",sourceCandidates,
      "; receipt=",outPath,"\n");
QUIT;
