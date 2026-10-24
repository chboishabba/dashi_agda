# Reproducible acquisition helper for the ATLAS 12-dimensional GF(3)
# representation of 2.Suz:2 used by the Monster 3B normalizer construction.
#
# Requires GAP + AtlasRep.  This script ACQUIRES the certified source matrices
# and emits machine-readable integer rows for the repository-side symplectic
# form/basis/field-candidate analyzer.

if LoadPackage("atlasrep", false) <> true then
  Error("AtlasRep package is required");
fi;

info := OneAtlasGeneratingSetInfo(
  "2.Suz.2",
  Dimension, 12,
  Characteristic, 3
);;

if info = fail then
  Error("ATLAS 12-dimensional GF(3) representation of 2.Suz:2 not found");
fi;

gens := AtlasGenerators(info).generators;;

IntMatrix := function(m)
  return List(m, row -> List(row, x -> IntFFE(x)));
end;

Print("group=2.Suz.2\n");
Print("field=GF(3)\n");
Print("dimension=12\n");
Print("generator_count=", Length(gens), "\n");
Print("representation_info=", info, "\n");

for i in [1..Length(gens)] do
  Print("generator_", i, "_int=", IntMatrix(gens[i]), "\n");
od;

# Independent Monster-normalizer source cross-check.  This is the representation
# used in Breuer--Magaard--Wilson Appendix 9.2; the lower-right 14x14 blocks
# generate 3_+^(1+12):2.Suz.2.
info38 := OneAtlasGeneratingSetInfo(
  "3^(1+12):6.Suz.2",
  Dimension, 38
);;

if info38 = fail then
  Error("ATLAS 38-dimensional Monster-normalizer representation not found");
fi;

gens38 := AtlasGenerators(info38).generators;;
Print("monster_normalizer_dimension=38\n");
Print("monster_normalizer_generator_count=", Length(gens38), "\n");
Print("monster_normalizer_info=", info38, "\n");
