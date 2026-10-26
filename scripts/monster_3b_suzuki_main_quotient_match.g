# Same-object character-table matcher for the Barraclough--Wilson 729-extension
# x 6.Suz multiplicity construction.
#
# This producer deliberately avoids guessing whether the selected Suzuki
# central phase equals or is inverse to the selected extraspecial phase.
# Instead it works at the outer-paired level and lets the published quotient
# maps decide which split main-table constituent descends to N(3B).
#
# PRIMARY MATHEMATICAL / COMPUTATIONAL SOURCE
# R. W. Barraclough and R. A. Wilson,
# "The Character Table of a Maximal Subgroup of the Monster",
# LMS J. Comput. Math. 10 (2007), 161--175.
# DOI: 10.1112/S1461157000001352.
#
# PRIMARY COMPUTATIONAL PRECURSOR
# Richard William Barraclough,
# "Some Calculations Related To The Monster Group",
# PhD thesis, University of Birmingham, 2005, Section 5.3.
# No DOI asserted.
#
# REQUIRED TABLE/FUSION OBJECTS
#   6.Suz -> 6.Suz.2                         subgroup fusion
#   3^1+12:6.Suz.2 -> 6.Suz.2              quotient map
#   3^1+12:6.Suz.2 -> 3^1+12.2.Suz.2       qGtoN3B quotient map
#   3^1+12.2.Suz.2 -> M                     stored Monster fusion
#
# The producer fails closed if any map is unavailable or ambiguous.

if LoadPackage("ctbllib") <> true then
  Error("CTblLib is required");
fi;

Read("scripts/monster_3b_source_json_escape.g");
six := CharacterTable("6.Suz");
outer := CharacterTable("6.Suz.2");
main := CharacterTable("3^1+12:6.Suz.2");
mn3b := CharacterTable("MN3B");
if mn3b = fail then
  mn3b := CharacterTable("3^1+12.2.Suz.2");
fi;
monster := CharacterTable("M");
if ForAny([six, outer, main, mn3b, monster], t -> t = fail) then
  Error("one or more required CTblLib tables are unavailable");
fi;

sixIrr := Irr(six);
outerIrr := Irr(outer);
mainIrr := Irr(main);
mn3bIrr := Irr(mn3b);
monsterIrr := Irr(monster);

sixLabels := AtlasLabelsOfIrreducibles(six, "short");
if sixLabels = fail or Length(sixLabels) <> Length(sixIrr) then
  Error("6.Suz ATLAS labels are unavailable or misaligned");
fi;

# ----------------------------------------------------------------------
# Exact maps.  No PossibleClassFusions fallback is allowed here.
# ----------------------------------------------------------------------

sixToOuter := GetFusionMap(six, outer);
if sixToOuter = fail then
  sixToOuter := FusionConjugacyClasses(six, outer);
fi;
if sixToOuter = fail then
  Error("6.Suz -> 6.Suz.2 fusion unavailable");
fi;

mainToOuter := GetFusionMap(main, outer);
if mainToOuter = fail then
  Error("main -> 6.Suz.2 quotient map unavailable");
fi;

mainToMN3B := GetFusionMap(main, mn3b);
if mainToMN3B = fail then
  Error("main -> MN3B quotient map unavailable; primary qGtoN3B data required");
fi;

mn3bToMonster := GetFusionMap(mn3b, monster);
if mn3bToMonster = fail then
  Error("MN3B -> Monster fusion unavailable");
fi;

# ----------------------------------------------------------------------
# Source-faithful 12 family and ALL degree-78 candidate families.
# Barraclough--Wilson Section 5.1 permits ANY eta in Irr(6.Suz).
# Thus DO NOT preselect a faithful degree78 before the exact quotient
# and Monster-character occurrence test. Nebe's Sym²12=78 is
# nonfaithful to 6.Suz and must remain in the search.
# ----------------------------------------------------------------------

IsFaithfulCharacter := function(chi)
  return ClassPositionsOfKernel(chi) = [1];
end;

p12 := Filtered([1..Length(sixIrr)], i ->
  sixIrr[i][1] = 12 and IsFaithfulCharacter(sixIrr[i]));
all78 := Filtered([1..Length(sixIrr)], i -> sixIrr[i][1] = 78);
if Length(p12) <> 2 or Length(all78) < 2 then
  Error("faithful 12 pair or source degree78 candidate inventory unavailable");
fi;
# CTblLib ATLAS-published 6.Suz table identity, independently recorded.
# Fail before claiming the current source class positions are canonical.
if Size(six) <> 2690072985600 or NrConjugacyClasses(six) <> 210 then
  Error("6.Suz source order/class count mismatch published CTblLib head");
fi;
sum12 := sixIrr[p12[1]] + sixIrr[p12[2]];

# ----------------------------------------------------------------------

# Identify outer character pairs via FULL class-function restriction,
# without assuming which 78 family occurs in the Monster quotient.
# ----------------------------------------------------------------------

OuterRestriction := function(chi)
  return ClassFunction(six, List(sixToOuter, c -> chi[c]));
end;

outer12Pair := Filtered([1..Length(outerIrr)], i ->
  outerIrr[i][1] = 24 and OuterRestriction(outerIrr[i]) = sum12);
if Length(outer12Pair) <> 1 then
  Error("expected one 6.Suz.2 character restricting to faithful12a+12b");
fi;
outer12Pos := outer12Pair[1];

Pair78OnSix := function(outerPos)
  local restricted, multiplicities, support;
  restricted := OuterRestriction(outerIrr[outerPos]);
  multiplicities := List(sixIrr, chi -> ScalarProduct(six, restricted, chi));
  if ForAny(multiplicities, x -> not IsInt(x) or x < 0) then
    Error("outer degree156 restriction is not a nonnegative six-Suz character");
  fi;
  support := Filtered([1..Length(multiplicities)], k -> multiplicities[k] <> 0);
  if Length(support) <> 2 or
     ForAny(support, k -> sixIrr[k][1] <> 78 or multiplicities[k] <> 1) then
    return fail;
  fi;
  return support;
end;

outer78Families := [];
for i in [1..Length(outerIrr)] do
  if outerIrr[i][1] = 156 then
    pair := Pair78OnSix(i);
    if pair <> fail then
      Add(outer78Families, rec(outerPos:=i, sixPositions:=pair));
    fi;
  fi;
od;
if Length(outer78Families) = 0 then
  Error("no source 6.Suz.2 degree156 characters restrict to 78+78");
fi;

# ----------------------------------------------------------------------

# Identify Barraclough's fused degree-1458 main-table character.
#
# The extraspecial centre is NOT selected merely by order and class size.  The
# main group also contains the 3-part of the 6.Suz centre and diagonal products.
# The exact extraspecial central class is the size-two order-three class in the
# kernel of the main -> 6.Suz.2 quotient.
# ----------------------------------------------------------------------

mainOrders := OrdersClassRepresentatives(main);
mainSizes := SizesConjugacyClasses(main);
extraspecialCentralCandidates := Filtered([1..Length(mainOrders)], i ->
  mainOrders[i] = 3 and mainSizes[i] = 2 and mainToOuter[i] = 1);
if Length(extraspecialCentralCandidates) <> 1 then
  Error("expected one size-two order-three extraspecial central class in ker(main -> 6.Suz.2)");
fi;
mainCentral3 := extraspecialCentralCandidates[1];

# Expose the nonidentity order-three class in the qGtoN3B kernel separately.
# This is the exact future discriminator for <t1*t2> versus <t1*t2^-1>.
qKernelCandidates := Filtered([1..Length(mainOrders)], i ->
  mainOrders[i] = 3 and mainSizes[i] = 2 and mainToMN3B[i] = 1);
if Length(qKernelCandidates) <> 1 then
  Error("expected one size-two order-three nonidentity class in ker(main -> MN3B)");
fi;
qKernel3 := qKernelCandidates[1];
qKernelOuterClass := mainToOuter[qKernel3];
# INDEPENDENT PUBLISHED SOURCE VERIFICATION, not a new convention:
# Breuer--Magaard--Wilson, "Some steps in the verification of the
# ordinary character table of the Monster group" (12 Dec 2024),
# §6: H/[1,19] fails restricted-196883 character decomposition
# (95 candidates, rank88, SolutionMat = fail). H/[1,20] has a
# decomposition and is equivalent to the stored MN3B table.
# https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm
# Original Barraclough--Wilson (2007) quotient source remains primary.
# The current main-table identity fixes the ORIGINAL class positions;
# do not apply these integers to arbitrarily permuted class tables.
if qKernel3 <> 20 or qKernelOuterClass <> 6 then
  Error("main->MN3B quotient disagrees with original BW and BMW24 class20 selection");
fi;
outerOrders := OrdersClassRepresentatives(outer);
if outerOrders[qKernelOuterClass] <> 3 then
  Error("qGtoN3B kernel class does not project to an order-three 6.Suz.2 class");
fi;

base1458Candidates := Filtered([1..Length(mainIrr)], i ->
  mainIrr[i][1] = 1458 and mainIrr[i][mainCentral3] = -729);
if Length(base1458Candidates) <> 1 then
  Error("degree-1458 fused Heisenberg character was not uniquely identified by extraspecial central trace -729");
fi;
base1458Pos := base1458Candidates[1];
base1458 := mainIrr[base1458Pos];

# **Exact source negative control from the central-phase pair**.
# The fused 1458 character contains both nontrivial E-centre eigenspaces
# of dimension729. A 6.Suz.2 OUTER element inverting that centre must
# exchange these eigenspaces, hence have trace ZERO. Identify the
# quotient C2 character by its full restriction to the 6.Suz subgroup,
# rather than guessing its Atlas label or class positions. This is a
# necessary SOURCE character-table screen; it does not select the
# Monster 78 family, the source r word, or the normalizer Hom.
outerSignCandidates := Filtered([1..Length(outerIrr)], j ->
  outerIrr[j][1]=1 and
  ForAll(sixToOuter, c -> outerIrr[j][c]=1) and
  ForAny([1..NrConjugacyClasses(outer)], c -> outerIrr[j][c]<>1));
if Length(outerSignCandidates)<>1 then
  Error("cannot identify unique source 6.Suz.2/6.Suz outer sign");
fi;
outerSign := outerIrr[outerSignCandidates[1]];
if ForAny([1..NrConjugacyClasses(outer)], c ->
    not (outerSign[c]=1 or outerSign[c]=-1)) then
  Error("source outer sign must be C2-valued");
fi;
outerInvertingMainPositions := Filtered([1..Length(mainOrders)], c ->
  outerSign[mainToOuter[c]]=-1);
if Length(outerInvertingMainPositions)=0 then
  Error("no original main-table centre-inverting outer-coset classes");
fi;
if ForAny(outerInvertingMainPositions, c -> base1458[c]<>0) then
  Error("source fused 1458 character nonzero on centre-inverting coset");
fi;


# ----------------------------------------------------------------------
# Inflate the outer-paired Suzuki characters through main -> 6.Suz.2,
# multiply by the fused 1458 character, and decompose in Irr(main).
# ----------------------------------------------------------------------

InflateOuterToMain := function(chi)
  return ClassFunction(main, List(mainToOuter, c -> chi[c]));
end;

ProductCharacter := function(left, right)
  return ClassFunction(main,
    List([1..Length(mainOrders)], c -> left[c] * right[c]));
end;

DecomposeMain := function(chi)
  local coeffs, support;
  coeffs := List(mainIrr, psi -> ScalarProduct(main, chi, psi));
  if ForAny(coeffs, x -> not IsInt(x) or x < 0) then
    Error("main-table product did not decompose with nonnegative integral multiplicities");
  fi;
  support := Filtered([1..Length(coeffs)], i -> coeffs[i] <> 0);
  return rec(coeffs := coeffs, support := support);
end;

prod12 := ProductCharacter(base1458, InflateOuterToMain(outerIrr[outer12Pos]));
dec12 := DecomposeMain(prod12);
if Length(dec12.support) <> 2 or
   ForAny(dec12.support, i -> dec12.coeffs[i] <> 1 or mainIrr[i][1] <> 17496) then
  Error("1458 x faithful12 outer pair did not split into two degree17496 rows");
fi;

# ----------------------------------------------------------------------

# Determine descent through qGtoN3B by exact full class-function pullback.
# This is the quotient-kernel compatibility test; no phase equality is guessed.
# ----------------------------------------------------------------------

PullbackMN3B := function(chi)
  return ClassFunction(main, List(mainToMN3B, c -> chi[c]));
end;

FindMN3BDescent := function(mainPos)
  local matches;
  matches := Filtered([1..Length(mn3bIrr)], j ->
    PullbackMN3B(mn3bIrr[j]) = mainIrr[mainPos]);
  if Length(matches) = 0 then
    return fail;
  fi;
  if Length(matches) <> 1 then
    Error("main irreducible matches more than one MN3B pullback");
  fi;
  return matches[1];
end;

desc12 := List(dec12.support, FindMN3BDescent);
paid12 := Filtered([1..Length(desc12)], k -> desc12[k] <> fail);
if Length(paid12) <> 1 then
  Error("expected one degree17496 main constituent to descend to MN3B");
fi;
main12DescendingPos := dec12.support[paid12[1]];
mn3b12Pos := desc12[paid12[1]];

# Use the ACTUAL restricted Monster character to SELECT the 78 family,
# instead of presupposing faithful/nonfaithful 6.Suz irreducibles.
monster196883 := Filtered([1..Length(monsterIrr)], i ->
  monsterIrr[i][1] = 196883);
if Length(monster196883) <> 1 then
  Error("expected unique Monster degree196883 character");
fi;
restrictedMonster := ClassFunction(mn3b,
  List(mn3bToMonster, c -> monsterIrr[monster196883[1]][c]));
monsterMults := List(mn3bIrr, psi -> ScalarProduct(mn3b, restrictedMonster, psi));

surviving78Families := [];
for family in outer78Families do
  product78 := ProductCharacter(base1458,
    InflateOuterToMain(outerIrr[family.outerPos]));
  trial78 := DecomposeMain(product78);
  if Length(trial78.support) = 2 and
     ForAll(trial78.support, i ->
       trial78.coeffs[i] = 1 and mainIrr[i][1] = 113724) then
    trialDesc78 := List(trial78.support, FindMN3BDescent);
    trialPaid78 := Filtered([1..Length(trialDesc78)],
                           k -> trialDesc78[k] <> fail);
    if Length(trialPaid78) = 1 then
      trialMN3B := trialDesc78[trialPaid78[1]];
      if IsInt(monsterMults[trialMN3B]) and
         monsterMults[trialMN3B] > 0 then
        Add(surviving78Families,
          rec(outerPos:=family.outerPos,
              sixPositions:=family.sixPositions,
              split:=trial78,
              descend:=trialDesc78,
              paid:=trialPaid78));
      fi;
    fi;
  fi;
od;
if Length(surviving78Families) <> 1 then
  Error("Monster full-character restriction did not select exactly ONE degree78 family");
fi;
selected78 := surviving78Families[1];
outer78Pos := selected78.outerPos;
p78 := selected78.sixPositions;
dec78 := selected78.split;
desc78 := selected78.descend;
paid78 := selected78.paid;
main78DescendingPos := dec78.support[paid78[1]];
mn3b78Pos := desc78[paid78[1]];

# THE DECISIVE full-character comparison, on the ACTUAL selected 78
# family.  Both direct Sym² and contragredient Sym² of the source
# faithful12 are tested across all 6.Suz classes using the real
# second-power map, not centre signs, zeta phase counts or dimensions.
powerMap2Six := PowerMap(six, 2);
if powerMap2Six = fail or Length(powerMap2Six) <> Length(OrdersClassRepresentatives(six)) then
  Error("source 6.Suz second power map not available for Sym² equality");
fi;
selectedDirectSym2Pairs := [];
selectedDualSym2Pairs := [];
for i in p12 do
  symValues := List([1..Length(powerMap2Six)], k ->
    (sixIrr[i][k]^2 + sixIrr[i][powerMap2Six[k]]) / 2);
  dualValues := List(symValues, v -> GaloisCyc(v,-1));
  if symValues[1] <> 78 or dualValues[1] <> 78 then
    Error("degree12 second symmetrization/dual did not have degree78");
  fi;
  for j in p78 do
    if symValues = List(sixIrr[j],v -> v) then
      Add(selectedDirectSym2Pairs,[i,j]);
    fi;
    if dualValues = List(sixIrr[j],v -> v) then
      Add(selectedDualSym2Pairs,[i,j]);
    fi;
  od;
od;
selectedDirectSym2Count := Length(selectedDirectSym2Pairs);
selectedDualSym2Count := Length(selectedDualSym2Pairs);
if selectedDirectSym2Count > 2 or selectedDualSym2Count > 2 then
  Error("unexpected multiple full-character Sym²12 matches");
fi;
# The FAMILY has both conjugate halves; direct/dual matching at this
# level should be all-or-none. Keep failure explicit rather than a
# partial equality that happens to match just one half.
if selectedDirectSym2Count = 1 or selectedDualSym2Count = 1 then
  Error("partial selected conjugate78 Sym² family equality");
fi;
selected78IsNebeSym2Family :=
  selectedDirectSym2Count = 2 and selectedDualSym2Count = 2;

# Exact 6.Suz central involution signature is an independent discriminator.
# A faithful 12 contributes -12. A faithful78 contributes -78, while
# Nebe's Sym²(faithful12) contributes +78; do not fix either in advance.
central2Classes := Filtered(ClassPositionsOfCentre(six), i ->
  OrdersClassRepresentatives(six)[i] = 2);
if Length(central2Classes) <> 1 then
  Error("central 6.Suz involution class unavailable");
fi;
central2Class := central2Classes[1];
if ForAny(p12, i -> sixIrr[i][central2Class] <> -12) then
  Error("source selected faithful12 did not have C2 trace -12");
fi;
if sixIrr[p78[1]][central2Class] <> sixIrr[p78[2]][central2Class] then
  Error("selected conjugate78 pair has inconsistent central C2 scalar");
fi;
# Scalar C3 fingerprints are compared on the SAME literal order-three
# centre class of 6.Suz. Existence of equal phases is NECESSARY for a
# common extended 729 action and common diagonal descent; it is NOT
# sufficient for actual source-coordinate same-object equivalence.
central3Classes := Filtered(ClassPositionsOfCentre(six), i ->
  OrdersClassRepresentatives(six)[i] = 3);
if Length(central3Classes) <> 2 then
  Error("exact two nonidentity central C3 Suzuki classes required");
fi;
central3Class := central3Classes[1];
common729C3MatchedPairs := [];
for i in p12 do
  for j in p78 do
    if sixIrr[i][central3Class] * 78 = sixIrr[j][central3Class] * 12 then
      Add(common729C3MatchedPairs, [i,j]);
    fi;
  od;
od;
common729C3PairCount := Length(common729C3MatchedPairs);
if common729C3PairCount > 2 then
  Error("unexpected excess central C3 alignments");
fi;

selected78C2Trace := sixIrr[p78[1]][central2Class];
if not (selected78C2Trace in [-78,78]) then
  Error("selected irreducible 78 is not central C2 scalar +/-1");
fi;
selected78Faithful := ForAll(p78, i -> IsFaithfulCharacter(sixIrr[i]));
selectedMultiplicityC2Trace := -12 + selected78C2Trace;
sym2CandidateMultiplicityC2Trace := -12 + 78;
selectedSym2C2Compatible :=
  selectedMultiplicityC2Trace = sym2CandidateMultiplicityC2Trace;
if selected78IsNebeSym2Family and not selectedSym2C2Compatible then
  Error("full selected Sym² family equality contradicts centre-C2 sign");
fi;

SourceBoolText := function(b)
  if b then return "true"; else return "false"; fi;
end;

# The independent ordinary-character exporter already emits these exact
# per-class coordinates. Emit them here TOO, from this literal table,
# so the downstream selected-character join can reject class permutations
# which preserve the table name, order, centre and Irr positions.
SixSuzJSONIntArray := function(xs)
  local result, k;
  result := "[";
  for k in [1..Length(xs)] do
    if k > 1 then Append(result, ","); fi;
    Append(result, String(xs[k]));
  od;
  Append(result, "]");
  return result;
end;

# ----------------------------------------------------------------------

# Same-object Monster restriction check.
# ----------------------------------------------------------------------

if not IsInt(monsterMults[mn3b12Pos]) or monsterMults[mn3b12Pos] <= 0 then
  Error("descended degree-17496 constituent does not occur in restricted Monster character");
fi;
if not IsInt(monsterMults[mn3b78Pos]) or monsterMults[mn3b78Pos] <= 0 then
  Error("descended degree-113724 constituent does not occur in restricted Monster character");
fi;

mn3bOrders := OrdersClassRepresentatives(mn3b);
mn3bSizes := SizesConjugacyClasses(mn3b);
mn3bCentralCandidates := Filtered([1..Length(mn3bOrders)], i ->
  mn3bOrders[i] = 3 and mn3bSizes[i] = 2);
if Length(mn3bCentralCandidates) <> 1 then
  Error("expected one size-two order-three MN3B class");
fi;
mn3bCentral3 := mn3bCentralCandidates[1];
if 2 * mn3bIrr[mn3b12Pos][mn3bCentral3] <> -mn3bIrr[mn3b12Pos][1] then
  Error("degree-17496 Monster constituent is not paired-phase at central 3B");
fi;
if 2 * mn3bIrr[mn3b78Pos][mn3bCentral3] <> -mn3bIrr[mn3b78Pos][1] then
  Error("degree-113724 Monster constituent is not paired-phase at central 3B");
fi;

output := OutputTextFile("build/monster_3b_suzuki_main_quotient_match.json", false);
SetPrintFormattingStatus(output, false);
PrintTo(output,
  "{\n",
  "  \"main_table\": \"", Identifier(main), "\",\n",
  "  \"mn3b_table\": \"", Identifier(mn3b), "\",\n",
  "  \"six_suz_table\": \"", Identifier(six), "\",\n",
  "  \"six_suz_group_order\": ", Size(six), ",\n",
  "  \"six_suz_class_count\": ", NrConjugacyClasses(six), ",\n",
  "  \"six_suz_class_orders\": ", SixSuzJSONIntArray(OrdersClassRepresentatives(six)), ",\n",
  "  \"six_suz_class_sizes\": ", SixSuzJSONIntArray(SizesConjugacyClasses(six)), ",\n",
  "  \"six_suz_power_map_2_zero_based\": ",
      SixSuzJSONIntArray(List(powerMap2Six, k -> k-1)), ",\n",
  "  \"six_suz_degree12_positions\": [", p12[1], ", ", p12[2], "],\n",
  "  \"six_suz_degree78_positions\": [", p78[1], ", ", p78[2], "],\n",
  "  \"six_suz_outer_table\": \"", Identifier(outer), "\",\n",
  "  \"base_1458_main_position\": ", base1458Pos, ",\n",
  "  \"base_1458_extraspecial_central_class_position\": ", mainCentral3, ",\n",
  "  \"base_1458_central_trace\": -729,\n",
  "  \"base_1458_outer_centre_inverting_trace_zero\": true,\n",
  "  \"qg_to_n3b_kernel_order_three_class_position\": ", qKernel3, ",\n",
  "  \"qg_to_n3b_kernel_outer_class_position\": ", qKernelOuterClass, ",\n",
  "  \"degree_12_atlas_labels\": [", Monster3BSourceJSONQuotedLabel(sixLabels[p12[1]]), ", ", Monster3BSourceJSONQuotedLabel(sixLabels[p12[2]]), "],\n",
  "  \"degree_78_atlas_labels\": [", Monster3BSourceJSONQuotedLabel(sixLabels[p78[1]]), ", ", Monster3BSourceJSONQuotedLabel(sixLabels[p78[2]]), "],\n",
  "  \"source_selected_degree_78_faithful_to_6Suz\": ", SourceBoolText(selected78Faithful), ",\n",
  "  \"suzuki_central_involution_class_position\": ", central2Class, ",\n",
  "  \"suzuki_central_order_three_class_position\": ", central3Class, ",\n",
  "  \"common_729_necessary_equal_C3_phase_pair_count\": ", common729C3PairCount, ",\n",
  "  \"selected_78_direct_sym2_full_character_pair_count\": ", selectedDirectSym2Count, ",\n",
  "  \"selected_78_dual_sym2_full_character_pair_count\": ", selectedDualSym2Count, ",\n",
  "  \"selected_78_is_nebe_sym2_family_full_character_equal\": ", SourceBoolText(selected78IsNebeSym2Family), ",\n",
  "  \"source_selected_S90_central_C2_trace\": ", selectedMultiplicityC2Trace, ",\n",
  "  \"sym2_candidate_S90_central_C2_trace\": ", sym2CandidateMultiplicityC2Trace, ",\n",
  "  \"source_selected_c2_compatible_with_sym2_faithful12\": ", SourceBoolText(selectedSym2C2Compatible), ",\n",
  "  \"outer_12_pair_position\": ", outer12Pos, ",\n",
  "  \"outer_78_pair_position\": ", outer78Pos, ",\n",
  "  \"main_12_split_positions\": [", dec12.support[1], ", ", dec12.support[2], "],\n",
  "  \"main_78_split_positions\": [", dec78.support[1], ", ", dec78.support[2], "],\n",
  "  \"main_12_descending_position\": ", main12DescendingPos, ",\n",
  "  \"main_78_descending_position\": ", main78DescendingPos, ",\n",
  "  \"mn3b_12_position\": ", mn3b12Pos, ",\n",
  "  \"mn3b_78_position\": ", mn3b78Pos, ",\n",
  "  \"mn3b_12_monster_multiplicity\": ", monsterMults[mn3b12Pos], ",\n",
  "  \"mn3b_78_monster_multiplicity\": ", monsterMults[mn3b78Pos], ",\n",
  "  \"extraspecial_centre_selected_by_outer_quotient_kernel\": true,\n",
  "  \"qg_to_n3b_kernel_class_identified\": true,\n",
  "  \"outer_pair_restriction_full_character_match\": true,\n",
  "  \"main_product_split_full_character_decomposition\": true,\n",
  "  \"quotient_descent_full_character_match\": true,\n",
  "  \"restricted_monster_same_object_match\": true,\n",
  "  \"diagonal_kernel_orientation_paid\": false,\n",
  "  \"individual_zeta_label_orientation_paid\": false\n",
  "}\n");
CloseStream(output);

Print("Monster 3B Suzuki/main quotient same-object match written.\n");
Print("base1458 main Irr position: ", base1458Pos, "\n");
Print("qGtoN3B nonidentity kernel class: ", qKernel3,
      "; outer image class: ", qKernelOuterClass, "\n");
Print("12ab -> main ", dec12.support, " -> descending MN3B Irr ", mn3b12Pos, "\n");
Print("78ab -> main ", dec78.support, " -> descending MN3B Irr ", mn3b78Pos, "\n");
QUIT;
