# Ternary Golay cross-pollination boundary

## External project attribution

The UBP concepts and source implementation studied by this tranche originate in:

- **Project:** *Universal Binary Principle — Research Repository*
- **Author:** **Euan R. A. Craig (DigitalEuan)**
- **Repository:** `DigitalEuan/UBP_Repo`
- **URL:** https://github.com/DigitalEuan/UBP_Repo
- **Branch:** `main`
- **Checkpoint:** `core_studio_v4.0/ubp_checkpoint_v5.4.1.md`
- **Unified core:** `core_studio_v4.0/core/ubp_unified_v5.py`
- **TGIC implementation:** `core_studio_v4.0/core/tgic_v3.py`

DASHI does not claim authorship of UBP, TGIC, TAX, NRCI, OffBit, GLR, or the source implementation. This branch is a derivative critical formalisation and mathematical cross-pollination effort.

## Explicit extended ternary Golay construction

`ExplicitCode729.agda` now replaces the former parameter-only boundary with a concrete systematic generator over DASHI's `TriTruth ≅ F3` field carrier:

```text
G = [ I6 | A ]

A =
2 0 2 1 1 2
2 1 1 2 0 2
2 2 0 2 1 1
2 2 1 1 2 0
2 1 2 0 2 1
0 1 1 1 1 1
```

The matrix is a systematic row reduction, with a coordinate permutation, of six independent rows from the order-12 Hadamard presentation described by:

- **Noam D. Elkies**, *The ternary Golay codes and related structures*, Harvard Math 256x extended lecture notes, no DOI recorded.

The construction is therefore correctly described as **Hadamard reduction modulo 3**, not as a ternary Hamming-code construction.

The local finite proof surface includes:

- a left inverse for the systematic encoder, hence injectivity of the six-symbol message map;
- exactly `3^6 = 729` enumerated messages/codewords;
- a zero Gram matrix for the six generator rows;
- no nonzero words of weight below six;
- the exact weight distribution

```text
weight 0  :   1
weight 6  : 264
weight 9  : 440
weight 12 :  24
```

These claims are intended to reduce in Agda rather than being imported from the citation.

## Exact weight enumerator

`TernaryGolayWeightEnumerator.agda` records and locally recomputes

\[
W_C(X,Y)=X^{12}+264X^6Y^6+440X^3Y^9+24Y^{12}.
\]

The external invariant-theory calibration is:

- **F. Jessie MacWilliams, Colin L. Mallows and N. J. A. Sloane**, *Generalizations of Gleason's theorem on weight enumerators of self-dual codes*, DOI `10.1109/TIT.1972.1054898`.

The Gleason theorem explains why the polynomial is forced for the appropriate extremal Type III self-dual code. It is not substituted for the exhaustive local computation.

## Small Witt design computed from supports

`SmallWittHexadCount.agda` does more than divide `264` by the sign-orbit size `2`.

It:

1. filters the 264 weight-six words;
2. maps each word to its Boolean support;
3. deduplicates those supports to exactly 132 hexads;
4. generates all

\[
\binom{12}{5}=792
\]

pentads;
5. checks exhaustively that every pentad is contained in exactly one computed hexad.

Thus the constructed support system satisfies the finite incidence condition for

\[
S(5,6,12).
\]

The associated uniqueness/design reference is:

- **Vera Pless**, *More on the uniqueness of the Golay codes*, DOI `10.1016/0012-365X(92)90569-2`.

The citation calibrates the equivalence class; the 132-support and unique-pentad checks are local computations.

## Binary/ternary MacWilliams common boundary

`BinaryTernaryMacWilliamsUnification.agda` introduces a common q-ary coefficient interface rather than duplicating unrelated prose arguments.

The primary source attached to that interface is:

- **F. Jessie MacWilliams**, *A Theorem on the Distribution of Weights in a Systematic Code*, DOI `10.1002/j.1538-7305.1963.tb04003.x`.

The module attaches:

- the binary reduced coefficient equation `64 * 759 = 48576`;
- the locally computed ternary `1/264/440/24` distribution;
- the ternary sign-orbit/support calculation `2 * 132 = 264`.

It explicitly does **not** claim that one undifferentiated proof automatically covers the `q=2` and `q=3` specialisations. The common transform schema is shared; the coefficient kernels remain field-specific.

## Genuine 9-to-3 arithmetic bridge

DASHI already has:

```text
TriTruth    ≅ F3
NonaryTruth ≅ Z/9Z
```

`NonaryTernaryReduction.agda` proves exhaustively that reduction modulo three preserves zero, one, addition and multiplication, with fibres:

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

Under full `S3`, all six directed channels form one orbit. Under the rotation subgroup `C3`, they split into cyclic and anti-cyclic triples. A transposition exchanges those two orientations.

Maps to `TriTruth`, `HexTruth` and `NonaryTruth` remain codecs unless operation preservation is proved.

## Exact TGIC Walsh extraction

From Euan R. A. Craig's attributed `tgic_v3.py`, the pairwise Walsh coefficients are:

```text
XY =  5/4 - Y/4
XZ = -1/80
YZ = -5/3
```

Their `S3` average is:

```text
-103/720 - Y/12
```

The nonzero residual quantifies the presentation bias introduced by assigning different Boolean operations to the three axis pairs. This remains an internal theorem about the source model, not a physical-energy theorem.

## UBP source table versus the canonical pi continued fraction

The attributed UBP source `core_studio_v4.0/core/ubp_unified_v5.py` supplies a coefficient list to `get_pi(50)`. `Pi50ConvergentTable.agda` preserves that source table exactly and compares it with:

- **N. J. A. Sloane**, *A001203: Simple continued fraction expansion of Pi*, OEIS, no DOI.

The lists agree through coefficient 47 and first differ at coefficient 48:

```text
attributed source coefficient 48 = 6
canonical pi coefficient 48     = 2
```

Consequently, the source rational is retained as the exact value computed by the external implementation, but is not renamed the genuine 50-coefficient convergent of pi.

The exact rationals recorded are:

```text
source p50 = 183157143516396120473427579101
source q50 =  58300729506452262642556705291

canonical p50 = 16397605394050964443746106649
canonical q50 =  5219519906667074477262822481
```

The canonical `q50*q51` continued-fraction error-bound denominator is also recorded. Constructive-real pi and the analytic error theorem remain explicit imports.

## Mandatory Calderbank-Sloane correction

The following original paper and correction are always paired:

- **A. R. Calderbank and N. J. A. Sloane**, *The Ternary Golay Code, the Integers mod 9, and the Coxeter-Todd Lattice*, DOI `10.1109/18.485733`;
- **A. R. Calderbank and N. J. A. Sloane**, *Correction to: The Ternary Golay Code, the Integers Mod 9 and the Coxeter-Todd Lattice*, DOI `10.1109/TIT.2002.806139`.

The corrected lattice has minimum norm 4, determinant `3^12` and centre-density denominator 729, and is **not** `K12`.

The valid arithmetic reduction `Z/9Z -> F3` survives; the withdrawn `Z9 lift -> K12` identification does not.

## Correct Coxeter-Todd and Mathieu routes

The branch retains explicit theorem interfaces for:

1. an order-three Leech fixed-sublattice route to `K12`;
2. an Eisenstein length-six repetition-code `B_c` route;
3. Golay trio orbits and stabilisers in `M24`;
4. dodecad/complement stabilisers and the 12-point Mathieu lane;
5. the `M12` action on the computed small-Witt hexads;
6. the order-two kernel of the monomial automorphism extension.

The actual group actions and lattice isometries remain theorem-import/construction obligations.

## Remaining frontier

The major remaining mathematical work is now narrower:

1. turn the zero-Gram, rank-six explicit code into a reusable abstract self-duality theorem rather than relying only on finite enumeration;
2. formalise puncturing and perfect radius-two decoding for the `[11,6,5]_3` code;
3. construct the `M12` permutation and `2.M12` monomial actions on the explicit code;
4. link the computed hexads to the Mathieu action, not merely the incidence design;
5. instantiate and compare the two valid Coxeter-Todd constructions;
6. supply constructive-real pi and transfer the canonical continued-fraction bound to the exact observer constant;
7. instantiate certified Leech dynamics and study connectivity, cycles, TAX monotonicity and path cocycles.

## Validation

Focused commands:

```text
python3 scripts/check_ternary_golay_cross_pollination.py

nix develop .# --command bash scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/TernaryGolay/Regression.agda
```

The workflow installs Nix before invoking the focused Agda aggregate. The PR remains draft until an observable Agda kernel receipt is green. No external physical, semantic, empirical or independent-replication authority follows from this tranche.
