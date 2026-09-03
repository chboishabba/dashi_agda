# Exact CTblLib probe for restrictions of the faithful degree-143 Suz character.
#
# PURPOSE
#   Test whether the published Suz-irreducible 143 can acquire an invariant
#   53-dimensional summand after restriction to structurally motivated maximal
#   subgroups.  This is the representation-theoretic firewall for the proposed
#   R_53 ~ J_27 + V_26 / 1+26+26 Albert lane.
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

# Every table below has a stored fusion into Suz in current CTblLib.
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

  Add(records, rec(
    name := name,
    nonzeroPositions := nz,
    degrees := constituentDegrees,
    multiplicities := constituentMultiplicities,
    hasIrrep26 := 26 in constituentDegrees,
    hasIrrep27 := 27 in constituentDegrees,
    hasIrrep53 := 53 in constituentDegrees,
    hasInvariant53Subsum := 53 in attainable53,
    hasAlbert27Plus26Irreps := (26 in constituentDegrees) and (27 in constituentDegrees),
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
    "\"has_invariant_53_subsum\": ", LowercaseString(String(r.hasInvariant53Subsum)), ", ",
    "\"has_albert_27_plus_26_irreps\": ", LowercaseString(String(r.hasAlbert27Plus26Irreps)), ", ",
    "\"attainable_up_to_53\": ", r.attainableUpTo53, "}"
  );
  if j < Length(records) then PrintTo(output, ","); fi;
  PrintTo(output, "\n");
od;

PrintTo(output, "  ]\n}\n");
CloseStream(output);

Print("Suz 143 subgroup restriction probe written to build/suz_143_subgroup_restriction_probe.json\n");
QUIT_GAP(0);
