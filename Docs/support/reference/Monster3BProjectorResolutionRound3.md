# Monster 3B projector resolution — Round 3

This tranche continues the finite projector-and-character route without constructing a dense `65610 x 65610` matrix.

## Concrete result

The model carrier remains

```text
X x Fin 90,   X = F3^6,   |X| = 729.
```

For every model basis vector, the projector indexed by its `X` coordinate has coefficient one. Any projector carrying an explicit proof that its weight differs from the basis weight has coefficient zero. The corresponding product coefficient is therefore zero, while every projector coefficient is idempotent.

The exact dimensional resolution is

```text
729 * 90 = 65610.
```

The evaluation map from translated multiplicity labels to model basis vectors has constructive left and right inverses and commutes with every standard translation.

Every one of the six standard nontrivial translations of `F3^6` is proved fixed-point-free, first on `X` and then on the complete `X x Fin 90` basis. This is the finite permutation-basis producer behind zero trace for those generators.

## Remaining representation theorem

This round proves the complete pointwise projector resolution on the finite model. It does not identify the certified Monster `zeta` eigenspace with that model. The next promotion still requires one of:

```text
actual MN3B extraspecial-kernel intertwiner
or
complete extraspecial class-character signature.
```

Only after that may the model theorem be promoted to

```text
W_zeta restricted to E = H_zeta tensor S_zeta,
dim S_zeta = 90.
```

The later `12 + 78` decomposition remains a character-inner-product calculation.

## Sources

- Audrey Terras, *Fourier Analysis on Finite Groups and Applications*, DOI `10.1017/CBO9780511626265`.
- R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, DOI `10.1112/S1461157000001352`.
- I. M. Isaacs, *Character Theory of Finite Groups*, ISBN `978-0-486-68014-9`; no DOI assigned.

## Validation

```bash
bash scripts/check_monster_3b_projector_resolution_round3.sh
```

No Agda-kernel or Actions success is asserted until an actual run is observed.
