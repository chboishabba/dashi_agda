# Exact CTblLib restriction of the 196883-dimensional Monster character
# to the 3B normalizer.  This script fails closed if the table, fusion,
# character, or integral decomposition cannot be recovered.

LoadPackage("ctbllib");

monster := CharacterTable("M");
mn3b := CharacterTable("MN3B");
if monster = fail or mn3b = fail then
  Error("required CTblLib tables M and MN3B are unavailable");
fi;

monsterIrr := Irr(monster);
monsterDegrees := List(monsterIrr, DegreeOfCharacter);
pos196883 := Positions(monsterDegrees, 196883);
if Length(pos196883) <> 1 then
  Error("expected exactly one Monster irreducible of degree 196883");
fi;
chi := monsterIrr[pos196883[1]];

fusion := GetFusionMap(mn3b, monster);
if fusion = fail then
  Error("stored MN3B -> M class fusion is unavailable");
fi;

restrictedValues := List(fusion, i -> ValuesOfClassFunction(chi)[i]);
restricted := ClassFunction(mn3b, restrictedValues);
mnIrr := Irr(mn3b);
mults := List(mnIrr, psi -> ScalarProduct(mn3b, restricted, psi));
if ForAny(mults, x -> not IsInt(x) or x < 0) then
  Error("restriction did not decompose with nonnegative integral multiplicities");
fi;

support := Filtered([1..Length(mults)], i -> mults[i] <> 0);
terms := List(support, i -> rec(
  index := i,
  multiplicity := mults[i],
  degree := DegreeOfCharacter(mnIrr[i]),
  contribution := mults[i] * DegreeOfCharacter(mnIrr[i])
));

if Sum(terms, t -> t.contribution) <> 196883 then
  Error("restricted-character dimensions do not sum to 196883");
fi;

Print("{\n");
Print("  \"monster_table\": \"", Identifier(monster), "\",\n");
Print("  \"normalizer_table\": \"", Identifier(mn3b), "\",\n");
Print("  \"monster_character_index\": ", pos196883[1], ",\n");
Print("  \"monster_character_degree\": 196883,\n");
Print("  \"fusion_class_count\": ", Length(fusion), ",\n");
Print("  \"terms\": [\n");
for j in [1..Length(terms)] do
  t := terms[j];
  Print("    {\"index\": ", t.index,
        ", \"multiplicity\": ", t.multiplicity,
        ", \"degree\": ", t.degree,
        ", \"contribution\": ", t.contribution, "}");
  if j < Length(terms) then Print(","); fi;
  Print("\n");
od;
Print("  ]\n");
Print("}\n");
QUIT;
