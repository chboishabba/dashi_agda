# GAP + CTblLib computation for the restriction of the 196883-dimensional
# Monster character to the 3B normalizer table MN3B.
#
# Run with:
#   gap -q scripts/monster_3b_normalizer_restriction.g
#
# The script fails closed if the required tables, fusion, or character are
# unavailable.  It writes JSON for the plotting/dashboard layer.

LoadPackage("ctbllib");

monster := CharacterTable("M");
mn3b := CharacterTable("MN3B");

if monster = fail then
  Error("CTblLib does not provide CharacterTable(\"M\")");
fi;
if mn3b = fail then
  Error("CTblLib does not provide CharacterTable(\"MN3B\")");
fi;

monsterIrr := Irr(monster);
positions := Filtered([1..Length(monsterIrr)],
  i -> monsterIrr[i][1] = 196883);

if Length(positions) <> 1 then
  Error("expected exactly one Monster irreducible of degree 196883");
fi;

chiPosition := positions[1];
chi := monsterIrr[chiPosition];

# RestrictedClassFunction uses a stored class fusion from MN3B into M.
restricted := RestrictedClassFunction(chi, mn3b);
if restricted = fail then
  Error("could not restrict the Monster character to MN3B; check stored fusion");
fi;

mn3bIrr := Irr(mn3b);
multiplicitiesMatrix := MatScalarProducts(mn3b, mn3bIrr, [restricted]);
multiplicities := List(multiplicitiesMatrix, row -> row[1]);

nonzero := Filtered([1..Length(multiplicities)],
  i -> multiplicities[i] <> 0);

reconstructedDegree := Sum(nonzero,
  i -> multiplicities[i] * mn3bIrr[i][1]);

if reconstructedDegree <> 196883 then
  Error("restriction decomposition does not reconstruct degree 196883");
fi;

records := List(nonzero, i -> rec(
  position := i,
  multiplicity := multiplicities[i],
  degree := mn3bIrr[i][1],
  contribution := multiplicities[i] * mn3bIrr[i][1]
));

# JSON output is deliberately numeric and source-faithful.  Names for
# constituents should be added only when CTblLib/ATLAS metadata owns them.
output := OutputTextFile("build/monster_3b_normalizer_restriction.json", false);
SetPrintFormattingStatus(output, false);
PrintTo(output,
  "{\n",
  "  \"source_table\": \"M\",\n",
  "  \"target_table\": \"MN3B\",\n",
  "  \"monster_character_position\": ", chiPosition, ",\n",
  "  \"monster_character_degree\": 196883,\n",
  "  \"reconstructed_degree\": ", reconstructedDegree, ",\n",
  "  \"constituents\": [\n"
);

for j in [1..Length(records)] do
  r := records[j];
  PrintTo(output,
    "    {\"position\": ", r.position,
    ", \"multiplicity\": ", r.multiplicity,
    ", \"degree\": ", r.degree,
    ", \"contribution\": ", r.contribution, "}"
  );
  if j < Length(records) then
    PrintTo(output, ",");
  fi;
  PrintTo(output, "\n");
od;

PrintTo(output, "  ]\n}\n");
CloseStream(output);

Print("MN3B restriction written to build/monster_3b_normalizer_restriction.json\n");
Print("Nonzero constituents: ", Length(records), "\n");
Print("Reconstructed degree: ", reconstructedDegree, "\n");
QUIT;
