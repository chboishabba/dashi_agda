# Exact CTblLib probe for restrictions of the faithful degree-143 Suz character.
#
# PURPOSE
#   Test two competing downstream structures after restricting the published
#   Suz-irreducible 143 to structurally motivated maximal subgroups:
#
#   (A) highest-priority G2(4) bridge:
#         143 |_ G2(4) ?= 65 + 78
#       where 65 and 78 are genuine ordinary G2(4) irreducible degrees;
#
#   (B) older Albert residual lane:
#         does any named subgroup expose an invariant dimension-53 summand,
#         especially through 27 + 26?
#
#   The script records the COMPLETE ordinary restriction decomposition.  It
#   does not identify a G2(4)-degree-78 constituent with Wilson's degree-78
#   multiplicity representation merely from matching degree; that is a later
#   same-object / cover-character comparison.
#
# PRIMARY SOURCES
#   R. A. Wilson, "The odd-local subgroups of the Monster",
#   J. Austral. Math. Soc. 44 (1988), 1--16.
#   DOI: 10.1017/S1446788700031323.
#
#   GAP Character Table Library / ATLAS stored class fusions.
#
# Run with:
#   mkdir -p build
#   gap -q scripts/suz_143_subgroup_restriction_probe.g

LoadPackage("ctbllib");

suz := CharacterTable("Suz");
if suz = fail then
  Error("CTblLib does not provide CharacterTable(\"Suz\")");
fi;

suzIrr := Irr(suz);
pos143 := Filtered([1..Length(suzIrr)], i -> suzIrr[i][1] = 143);
if Length(pos143) <> 1 then
  Error("expected exactly one irreducible Suz character of degree 143");
fi;
chi143Position := pos143[1];
chi143 := suzIrr[chi143Position];

# G2(4) is deliberately first: it is the strongest structural candidate.
# Every table below is expected to have a stored fusion into Suz in CTblLib.
candidateNames := [
  "G2(4)",
  "U5(2)",
  "2^1+6.u4q2",
  "3^5:M11",
  "J2.2"
];

# Return all attainable invariant subrepresentation dimensions <= limit from
# the actual semisimple irreducible-copy multiset of a restricted character.
AttainableDimensions := function(degrees, multiplicities, limit)
  local attainable, i, copy, old, s, d;
  attainable := [0];
  for i in [1..Length(degrees)] do
    d := degrees[i];
    for copy in [1..multiplicities[i]] do
      old := ShallowCopy(attainable);
      for s in old do
        if s + d <= limit then
          AddSet(attainable, s + d);
        fi;
      od;
    od;
  od;
  return attainable;
end;

records := [];
for name in candidateNames do
  sub := CharacterTable(name);
  if sub = fail then
    Error(Concatenation("CTblLib does not provide CharacterTable(\"", name, "\")"));
  fi;

  fusion := GetFusionMap(sub, suz);
  if fusion = fail then
    Error(Concatenation("stored class fusion ", name, " -> Suz is unavailable"));
  fi;

  restrictedValues := List(fusion, c -> chi143[c]);
  restricted := ClassFunction(sub, restrictedValues);
  subIrr := Irr(sub);
  mults := List(subIrr, psi -> ScalarProduct(sub, restricted, psi));

  if ForAny(mults, x -> not IsInt(x) or x < 0) then
    Error(Concatenation("non-integral or negative restriction multiplicity for ", name));
  fi;

  nz := Filtered([1..Length(mults)], i -> mults[i] <> 0);
  reconstructedDegree := Sum(nz, i -> mults[i] * subIrr[i][1]);
  if reconstructedDegree <> 143 then
    Error(Concatenation("restriction to ", name, " does not reconstruct degree 143"));
  fi;

  constituentDegrees := List(nz, i -> subIrr[i][1]);
  constituentMultiplicities := List(nz, i -> mults[i]);
  attainable53 := AttainableDimensions(constituentDegrees, constituentMultiplicities, 53);

  # Exact ordinary-character G2(4) target.  We only mark the Boolean here;
  # the script does not fail if it is false, because a negative answer is a
  # scientifically useful result rather than a producer failure.
  isG2 := name = "G2(4)";
  g2Exact65Plus78 :=
    isG2
    and Length(nz) = 2
    and constituentDegrees = [65, 78]
    and constituentMultiplicities = [1, 1];

  Add(records, rec(
    name := name,
    nonzeroPositions := nz,
    degrees := constituentDegrees,
    multiplicities := constituentMultiplicities,
    hasIrrep26 := 26 in constituentDegrees,
    hasIrrep27 := 27 in constituentDegrees,
    hasIrrep53 := 53 in constituentDegrees,
    hasIrrep65 := 65 in constituentDegrees,
    hasIrrep78 := 78 in constituentDegrees,
    hasInvariant53Subsum := 53 in attainable53,
    hasAlbert27Plus26Irreps := (26 in constituentDegrees) and (27 in constituentDegrees),
    exactG2SixtyFivePlusSeventyEight := g2Exact65Plus78,
    attainableUpTo53 := attainable53
  ));
od;

output := OutputTextFile("build/suz_143_subgroup_restriction_probe.json", false);
SetPrintFormattingStatus(output, false);
PrintTo(output,
  "{\n",
  "  \"source_table\": \"Suz\",\n",
  "  \"source_character_position\": ", chi143Position, ",\n",
  "  \"source_character_degree\": 143,\n",
  "  \"g2_priority_target\": \"143|G2(4) = 65 + 78\",\n",
  "  \"candidates\": [\n"
);

for j in [1..Length(records)] do
  r := records[j];
  PrintTo(output,
    "    {\"table\": \"", r.name, "\", ",
    "\"degrees\": ", r.degrees, ", ",
    "\"multiplicities\": ", r.multiplicities, ", ",
    "\"has_irrep_26\": ", LowercaseString(String(r.hasIrrep26)), ", ",
    "\"has_irrep_27\": ", LowercaseString(String(r.hasIrrep27)), ", ",
    "\"has_irrep_53\": ", LowercaseString(String(r.hasIrrep53)), ", ",
    "\"has_irrep_65\": ", LowercaseString(String(r.hasIrrep65)), ", ",
    "\"has_irrep_78\": ", LowercaseString(String(r.hasIrrep78)), ", ",
    "\"has_invariant_53_subsum\": ", LowercaseString(String(r.hasInvariant53Subsum)), ", ",
    "\"has_albert_27_plus_26_irreps\": ", LowercaseString(String(r.hasAlbert27Plus26Irreps)), ", ",
    "\"exact_g2_65_plus_78\": ", LowercaseString(String(r.exactG2SixtyFivePlusSeventyEight)), ", ",
    "\"attainable_up_to_53\": ", r.attainableUpTo53, "}"
  );
  if j < Length(records) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;

PrintTo(output, "  ]\n}\n");
CloseStream(output);

Print("Suz 143 subgroup restriction probe written to build/suz_143_subgroup_restriction_probe.json\n");
QUIT_GAP(0);
