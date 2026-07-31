# Ternary Golay cross-pollination boundary

## External project attribution

The UBP concepts and implementation studied by this tranche originate in:

- **Project:** Universal Binary Principle — Research Repository
- **Author:** Euan R. A. Craig (DigitalEuan)
- **Repository:** `DigitalEuan/UBP_Repo`
- **URL:** https://github.com/DigitalEuan/UBP_Repo
- **Default branch:** `main`
- **Checkpoint:** `core_studio_v4.0/ubp_checkpoint_v5.4.1.md`
- **Unified core:** `core_studio_v4.0/core/ubp_unified_v5.py`
- **TGIC implementation:** `core_studio_v4.0/core/tgic_v3.py`

DASHI does not claim authorship of UBP, TGIC, TAX, NRCI, OffBit, GLR, or the original source implementation. This branch is a derivative critical formalisation and mathematical cross-pollination effort.

## Corrected mathematical picture

The extended ternary Golay code belongs on a native ternary lane:

```text
F3 coefficients
    -> six-dimensional message carrier
    -> [12,6,6]_3 extended ternary Golay code
    -> punctured [11,6,5]_3 perfect-code boundary
    -> M12 / small-Witt support boundary
```

The standard parameter surface is:

```text
alphabet cardinality = 3
length               = 12
dimension            = 6
minimum distance     = 6
codeword count       = 3^6 = 729
```

These parameters are recorded locally. The generator matrix, injectivity, self-duality, minimum-distance, perfect-decoding, small-Witt, and automorphism theorems remain explicit proof obligations until formal imports or direct Agda proofs are supplied.

## Genuine 9-to-3 arithmetic bridge

DASHI already has:

```text
TriTruth    ~= F3
NonaryTruth ~= Z/9Z
```

`NonaryTernaryReduction.agda` now proves exhaustively that reduction modulo three preserves zero, one, addition, and multiplication. Each ternary value has a three-element fibre:

```text
0 <- {0,3,6}
1 <- {1,4,7}
2 <- {2,5,8}
```

This is a genuine ring-homomorphic 9-to-3 bridge. It is distinct from serialising nine TGIC channels into a nine-element display carrier.

## Corrected 3 + 6 = 9 channel geometry

For three axes, the nine ordered channels decompose into:

```text
3 diagonal self-channels
6 directed off-diagonal channels
```

Under the full `S3` action, the six off-diagonal channels form one orbit. Under the rotation subgroup `C3`, they split into two size-three orbits:

```text
cyclic:      X->Y, Y->Z, Z->X
anti-cyclic: Y->X, Z->Y, X->Z
```

This corrects the stronger but false claim that the two triples are separate `S3` orbits.

The maps to `TriTruth`, `HexTruth`, and `NonaryTruth` are codecs unless operation preservation is separately proved.

## Exact TGIC local Walsh extraction

From Euan R. A. Craig's attributed `tgic_v3.py`, the eight local bit-state costs were extracted as affine expressions in the declared observer constant. Their exact Walsh coefficients are recorded in `TGICWalshS3Decomposition.agda`.

The pairwise coefficients are unequal:

```text
XY =  5/4 - Y/4
XZ = -1/80
YZ = -5/3
```

Their `S3` average is:

```text
-103/720 - Y/12
```

and the anisotropic residuals sum to zero. This quantifies the presentation bias created by assigning different Boolean operations to the three axis pairs. It is an internal theorem about the source model, not a physical-energy theorem.

## The Calderbank-Sloane correction is mandatory

The following paper must never be cited alone as a valid `K12` construction:

- A. R. Calderbank and N. J. A. Sloane,
  *The Ternary Golay Code, the Integers mod 9, and the Coxeter-Todd Lattice*,
  DOI `10.1109/18.485733`.

The authors published:

- A. R. Calderbank and N. J. A. Sloane,
  *Correction to: The Ternary Golay Code, the Integers Mod 9 and the Coxeter-Todd Lattice*,
  DOI `10.1109/TIT.2002.806139`.

The correction states that the constructed lattice is **not** the Coxeter-Todd lattice. The corrected data recorded in Agda are:

```text
minimum norm              = 4
determinant               = 3^12
centre-density denominator = 729
identity with K12         = false
```

It also supplies an impossibility boundary for the stated block-`9I` integer generator family.

The arithmetic reduction `Z/9Z -> F3` remains valid; the withdrawn `Z9 lift -> K12` identification does not.

## Correct Coxeter-Todd routes

Two routes are retained as explicit theorem interfaces:

1. an order-three Leech-lattice fixed-sublattice route;
2. an Eisenstein length-six repetition-code `B_c` route.

The associated source atlas includes:

- N. J. A. Sloane,
  *The Coxeter-Todd Lattice, the Mitchell Group and Related Sphere Packings*,
  DOI `10.1017/S0305004100060746`;
- J. H. Conway and N. J. A. Sloane,
  *Sphere Packings, Lattices and Groups, Third Edition*,
  DOI `10.1007/978-1-4757-6568-7`.

The local invariant receipt records rank 12, Eisenstein rank 6, minimum norm 4, 756 minimal vectors, discriminant exponent 6, rootlessness, and automorphism-group order 78,382,080. The actual equivalences remain external theorem-import obligations.

## Mathieu bridges

The tranche exposes, without silently proving:

- the single-orbit theorem for Golay trios;
- trio stabilizer order 64,512 and orbit size 3,795;
- the `S3` block-permutation factor;
- the dodecad/complement stabilizer route from `M24` to the 12-point Mathieu lane;
- weight-six ternary Golay supports as the small-Witt hexad lane;
- the order-two kernel in the monomial-automorphism extension over `M12`.

Only the finite arithmetic

```text
64512 * 3795 = 244823040
```

is closed locally. Group actions, stabilizers, design identities, and exact sequences require explicit receipts from the named sources.

## Observer constant and dynamics frontiers

`YIntervalCertificate.agda` separates:

```text
exact irrational target Y
rational implementation constant Y50
certified interval containing Y
```

A concrete proof still requires the actual continued-fraction convergent, constructive-real pi, irrationality, and monotone interval transfer.

`LeechValidMoveSet.agda` replaces ambient coordinate flips with certified additive-lattice displacements and compositional paths. A binary-shadow XOR law or minimal-vector transition graph must be supplied explicitly before those become lattice-valid dynamics.

## Validation

The focused validation target is:

```text
python3 scripts/check_ternary_golay_cross_pollination.py
nix develop .# --command bash scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/TernaryGolay/Regression.agda
```

The branch remains draft until an observable Agda kernel receipt is green. No external physical, semantic, empirical, or independent-replication authority is claimed.
