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
# Source-native faithful 12a/b and 78a/b candidate families.
# ----------------------------------------------------------------------

IsFaithfulCharacter := function(chi)
  return ClassPositionsOfKernel(chi) = [1];
end;

p12 := Filtered([1..Length(sixIrr)], i ->
  sixIrr[i][1] = 12 and IsFaithfulCharacter(sixIrr[i]));
p78 := Filtered([1..Length(sixIrr)], i ->
  sixIrr[i][1] = 78 and IsFaithfulCharacter(sixIrr[i]));
if Length(p12) <> 2 or Length(p78) <> 2 then
  Error("expected exactly two faithful 12 and two faithful 78 characters in 6.Suz");
fi;

sum12 := sixIrr[p12[1]] + sixIrr[p12[2]];
sum78 := sixIrr[p78[1]] + sixIrr[p78[2]];

# Identify the outer irreducibles restricting exactly to the two conjugate
# Suzuki pairs.  This binds 12a/b -> one degree-24 6.Suz.2 character and
# 78a/b -> one degree-156 6.Suz.2 character by full class-function equality.
OuterRestriction := function(chi)
  return ClassFunction(six, List(sixToOuter, c -> chi[c]));
end;

outer12Pair := Filtered([1..Length(outerIrr)], i ->
  outerIrr[i][1] = 24 and OuterRestriction(outerIrr[i]) = sum12);
outer78Pair := Filtered([1..Length(outerIrr)], i ->
  outerIrr[i][1] = 156 and OuterRestriction(outerIrr[i]) = sum78);
if Length(outer12Pair) <> 1 then
  Error("expected one 6.Suz.2 character restricting to 12a+12b");
fi;
if Length(outer78Pair) <> 1 then
  Error("expected one 6.Suz.2 character restricting to 78a+78b");
fi;
outer12Pos := outer12Pair[1];
outer78Pos := outer78Pair[1];

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
prod78 := ProductCharacter(base1458, InflateOuterToMain(outerIrr[outer78Pos]));
dec12 := DecomposeMain(prod12);
dec78 := DecomposeMain(prod78);

if Sum(dec12.support, i -> dec12.coeffs[i] * mainIrr[i][1]) <> 1458 * 24 then
  Error("1458 x 24 product degree reconstruction failed");
fi;
if Sum(dec78.support, i -> dec78.coeffs[i] * mainIrr[i][1]) <> 1458 * 156 then
  Error("1458 x 156 product degree reconstruction failed");
fi;

# Source expectation: the outer-paired products split into two constituents of
# equal degree.  Keep this as an executable check, not an assumed row number.
if Length(dec12.support) <> 2 or
   ForAny(dec12.support, i -> dec12.coeffs[i] <> 1 or mainIrr[i][1] <> 17496) then
  Error("1458 x (12a+12b) did not split as two multiplicity-one degree-17496 main characters");
fi;
if Length(dec78.support) <> 2 or
   ForAny(dec78.support, i -> dec78.coeffs[i] <> 1 or mainIrr[i][1] <> 113724) then
  Error("1458 x (78a+78b) did not split as two multiplicity-one degree-113724 main characters");
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
desc78 := List(dec78.support, FindMN3BDescent);
paid12 := Filtered([1..Length(desc12)], k -> desc12[k] <> fail);
paid78 := Filtered([1..Length(desc78)], k -> desc78[k] <> fail);
if Length(paid12) <> 1 then
  Error("expected exactly one of the two degree-17496 main characters to descend to MN3B");
fi;
if Length(paid78) <> 1 then
  Error("expected exactly one of the two degree-113724 main characters to descend to MN3B");
fi;

main12DescendingPos := dec12.support[paid12[1]];
mn3b12Pos := desc12[paid12[1]];
main78DescendingPos := dec78.support[paid78[1]];
mn3b78Pos := desc78[paid78[1]];

# ----------------------------------------------------------------------
# Same-object Monster restriction check.
# ----------------------------------------------------------------------

monster196883 := Filtered([1..Length(monsterIrr)], i -> monsterIrr[i][1] = 196883);
if Length(monster196883) <> 1 then
  Error("expected exactly one Monster irreducible of degree 196883");
fi;
restrictedMonster := ClassFunction(mn3b,
  List(mn3bToMonster, c -> monsterIrr[monster196883[1]][c]));
monsterMults := List(mn3bIrr, psi -> ScalarProduct(mn3b, restrictedMonster, psi));
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
  "  \"six_suz_outer_table\": \"", Identifier(outer), "\",\n",
  "  \"base_1458_main_position\": ", base1458Pos, ",\n",
  "  \"base_1458_extraspecial_central_class_position\": ", mainCentral3, ",\n",
  "  \"base_1458_central_trace\": -729,\n",
  "  \"qg_to_n3b_kernel_order_three_class_position\": ", qKernel3, ",\n",
  "  \"qg_to_n3b_kernel_outer_class_position\": ", qKernelOuterClass, ",\n",
  "  \"degree_12_atlas_labels\": [\"", sixLabels[p12[1]], "\", \"", sixLabels[p12[2]], "\"],\n",
  "  \"degree_78_atlas_labels\": [\"", sixLabels[p78[1]], "\", \"", sixLabels[p78[2]], "\"],\n",
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
