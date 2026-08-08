# Monster 3B orbifold and local-module round 4

This tranche continues the finite Monster 3B model from PR #471 while correcting the authority of the earlier `196608 + 276` chart and implementing the proof-bearing algebra that can be completed before the actual `MN3B` kernel action is imported.

## Published FLM weight-two decomposition

The basis-dependent arithmetic identity

```text
196608 = 196560 + 24 + 24
196884 = 196608 + 276
```

is retained, but it is no longer treated as the FLM orbifold-sector decomposition.

The sourced decomposition is formalized as

```text
dim (V_Lambda^+)_2
  = 300 + 196560/2
  = 98580

dim ((V_Lambda^T)^+)_2
  = 24 * 4096
  = 98304

98580 + 98304 = 196884.
```

The conformal line is retained inside the untwisted invariant sector:

```text
98580 = 1 + 98579
196883 = 98579 + 98304
196884 = 1 + 196883.
```

`LeechWeightTwo196608AuthorityCorrectionExact.agda` proves that the `196608` coordinate subtotal is unequal to both published orbifold summands. Equal total dimension does not transport an action, an invariant filtration, or a Monster submodule.

## Weight-one removal and conformal excitation index

The finite profile separates

```text
Leech weight-one currents: Fin 24
untwisted invariant weight one: Fin 0
twisted retained weight one: Fin 0
orbifold weight one: Fin 0 + Fin 0.
```

A generic theorem proves that a direct sum of two empty sectors is empty. Weight two is represented by `Fin 196884` and is inhabited, so the finite conformal excitation index is exactly two.

This formalizes the meaning of Moonshine "mass restoration" used in the discussion:

```text
orbifold removal of weight-one states
+ twisted completion
+ first surviving positive conformal grade at two.
```

The boundary explicitly refuses the promotion

```text
conformal excitation index 2
=> four-dimensional Yang--Mills Hamiltonian mass gap.
```

Such a bridge still needs a physical Hilbert-space functor, an operator intertwiner, cutoff/units, continuum stability and a dimensionful scale-generation mechanism.

## Order-three orbifold siblings

The two sourced Monster 3-local shapes are represented as distinct typed objects with one common origin:

```text
3^(1+12).2.Suz:2
3^8.Omega_8^-(3).2.
```

The extraspecial chart carries internal rank six and multiplicity ninety; the elementary chart carries rank eight and multiplicity ten. Both reconstruct the same `65610` sector:

```text
90 * 3^6 = 10 * 3^8 = 65610.
```

Their kernel and quotient geometries are proved distinct. The common orbifold origin and equal represented dimension do not construct a group isomorphism or a representation intertwiner.

## Model multiplicity space and exact promotion object

The finite multiplicity space is now literal:

```text
H_model = F3^6
S_model = Fin 90
H_model x S_model ~= ZetaModelBasis.
```

The evaluation and recovery maps have constructive two-sided inverses. Every multiplicity coordinate gives a translation-equivariant embedding of the Schrödinger basis.

`ActualZetaSectorRecognition W` is the minimized promotion input. It requires one two-sided model equivalence and one intertwining law for the six translations. From that single object the code derives:

- the actual weight coordinate;
- the actual multiplicity coordinate;
- transported characteristic projectors;
- own-weight projector coefficient one;
- translation covariance;
- fixed-point-freedom of every standard translation.

The repository still does not claim that the actual Monster zeta sector inhabits this recognition object.

## Exact extraspecial character criterion

The full model character signature is represented coefficientwise in the cyclotomic basis `1,zeta,zeta^2`:

```text
identity:        65610
central zeta:    65610 zeta
central zeta^2:  65610 zeta^2
noncentral:      0.
```

It is proved pointwise to be ninety copies of the `729`-dimensional Heisenberg signature. An actual class certificate must classify every kernel class and prove its trace equals this signature. The `MN3B` class coverage and the resulting actual intertwiner remain open.

## Cocycle-corrected normalizer action

The `C3` phase group is implemented with multiplication, inverse, associativity and inverse laws.

A generic theorem proves the required normalizer mechanism:

```text
Heisenberg action has cocycle c
multiplicity action has inverse cocycle c^-1
opposite phases cancel on pure tensors
------------------------------------------------
tensor action is honest on pure tensors.
```

This is the exact algebra needed after Stone--von Neumann recognition. No normalizer matrices or actual multiplicity character are fabricated.

## Remaining highest-alpha frontier

The next irreducible data are:

1. identify the actual extraspecial kernel classes inside `MN3B`;
2. certify the complete cyclotomic character signature on those classes;
3. construct `ActualZetaSectorRecognition W_zeta`;
4. transport the finite projector resolution to `W_zeta`;
5. construct the inertia-group action and its compensating cocycle on `Fin 90` or the actual multiplicity space;
6. calculate the actual multiplicity character;
7. prove or refute an actual `12 + 78` decomposition by character inner products and an intertwiner.

The numerical equality `90 = 12 + 78` remains insufficient by itself.

## Sources

- Igor B. Frenkel, James Lepowsky and Arne Meurman, *Vertex Operator Algebras and the Monster*, ISBN `978-0-12-267065-7`; no DOI assigned.
- Scott Carnahan, *51 constructions of the Moonshine module*, DOI `10.4310/CNTP.2018.v12.n2.a3`, arXiv `1707.02954`.
- Michael P. Tuite, *On the relationship between monstrous Moonshine and the uniqueness of the Moonshine module*, DOI `10.1007/BF02099885`, arXiv `hep-th/9305057`.
- Hsian-Yang Chen, Ching Hung Lam and Hiroki Shimakura, *Z_3-orbifold construction of the Moonshine vertex operator algebra and some maximal 3-local subgroups of the Monster*, DOI `10.1007/s00209-017-1878-z`.
- Toshiyuki Abe, Ching Hung Lam and Hiromichi Yamada, *A remark on Z_p-orbifold constructions of the Moonshine vertex operator algebra*, arXiv `1705.09022`; no DOI assigned here.
- R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, DOI `10.1112/S1461157000001352`.
- Jean-Pierre Serre, *Linear Representations of Finite Groups*, DOI `10.1007/978-1-4684-9458-7`.
- Audrey Terras, *Fourier Analysis on Finite Groups and Applications*, DOI `10.1017/CBO9780511626265`.

## Validation

```bash
bash scripts/check_monster_3b_orbifold_local_module_round4.sh
```

The checker cascades through Round 3, rejects holes and trust escapes, binds theorem markers to their owning files, and invokes the pinned Agda 2.9 runner on both the cumulative validation root and the top-level aggregate extension.
