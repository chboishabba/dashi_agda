# Monster 3B normalizer: exact restriction, Heisenberg multiplicity, and Leech weight-two bridge

This lane replaces decorative dimension plots with reproducible character-table calculations, exhaustive finite-Heisenberg checks, and kernel-checked arithmetic boundaries.

## Primary sources

- R. W. Barraclough and R. A. Wilson, **“The Character Table of a Maximal Subgroup of the Monster”**, *LMS Journal of Computation and Mathematics* 10 (2007), 161–175. DOI: `10.1112/S1461157000001352`.
- Robert A. Wilson, Peter Walsh, Richard A. Parker and Stephen Linton, **“A computer construction of the Monster”**, *Journal of Group Theory* 1 (1998), 307–337. DOI: `10.1515/jgth.1998.023`.
- Hsian-Yang Chen, Ching Hung Lam and Hiroki Shimakura, **“Z₃-orbifold construction of the Moonshine vertex operator algebra and some maximal 3-local subgroups of the Monster”**, *Mathematische Zeitschrift* 288 (2018), 75–100. DOI: `10.1007/s00209-017-1878-z`.
- Hiroki Shimakura, **“An E₈-approach to the moonshine vertex operator algebra”**, *Journal of the London Mathematical Society* 83 (2011), 493–516. DOI: `10.1112/jlms/jdq078`.
- John H. Conway and Simon P. Norton, **“Monstrous Moonshine”**, *Bulletin of the London Mathematical Society* 11 (1979), 308–339. DOI: `10.1112/blms/11.3.308`.
- Igor B. Frenkel, James Lepowsky and Arne Meurman, **“Vertex Operator Algebras and the Monster”**, Academic Press, 1988. ISBN `978-0-12-267065-7`; no DOI asserted.

## One-command validation

```bash
bash scripts/check_monster_3b_normalizer_dashboard.sh
```

The checker always:

1. compiles the Python producers;
2. exhaustively validates the explicit finite-Heisenberg model;
3. generates the structural function plots;
4. rejects postulates and trust escapes in the new Agda lane.

When GAP and CTblLib are installed it additionally:

1. restricts the unique degree-`196883` Monster character to `MN3B`;
2. checks nonnegative integral multiplicities;
3. reconstructs the restricted character on **every MN3B conjugacy class**;
4. identifies the size-two order-three class fusing to Monster `3B`;
5. verifies trace `53` and multiplicities `(65663,65610,65610)`;
6. emits JSON and a generated Agda certificate;
7. generates a one-cell-per-dimension sheet of the actual CTblLib restriction.

The GitHub workflow `.github/workflows/monster-3b-normalizer.yml` installs GAP and `gap-character-tables`, runs this checker, and uploads all certificates and figures.

## Exact CTblLib computation

The producer is:

```text
scripts/monster_3b_normalizer_restriction.g
```

It loads the Monster table and the 3B-normalizer table under any supported alias:

```gap
CharacterTable("M")
CharacterTable("MN3B")
CharacterTable("3^(1+12).2.Suz.2")
```

It then checks:

```text
monster196883CharacterUnique
mn3bToMonsterFusionAvailable
restrictionMultiplicitiesIntegral
restrictionMultiplicitiesNonnegative
restrictionDegreeReconstructs196883
restrictionReconstructsClasswise
mn3bCentralOrderThreeClass
mn3bCentralClassFusesToMonster3B
monster196883ValueOn3BIs53
```

The numeric certificate is:

```text
build/monster_3b_normalizer_restriction.json
```

The renderer

```text
scripts/render_monster_3b_certificate.py
```

independently validates the JSON schema and emits:

```text
build/generated/DASHI/Moonshine/Generated/Monster3BRestrictionCertificate.agda
```

The generated module kernel-checks:

```text
65663 + 65610 + 65610 = 196883
65610 + 53 = 65663
3 × 65610 + 53 = 196883
```

No constituent receives a semantic label such as `12`, `78`, `90`, or `3^6` merely from a coincident degree.

## Exact C₃ Fourier and integer-functional chart

`DASHI/Moonshine/Monster3BCyclicFourierDyadicBridgeExact.agda` records the 3B multiplicity vector

```text
(65663,65610,65610)
```

and the exact decomposition

```text
(65663,65610,65610)
  = 65536(1,1,1) + (127,74,74).
```

Therefore:

```text
196883 = 196608 + 275
53     = 127 - 74
```

and after adding the conformal line:

```text
196884 = 196608 + 276
54     = 128 - 74.
```

The same file reconciles the previously separate all-1, all-2, all-3, ordered `1,2,3`, reversed `3,2,1`, and `3,6,9` probes:

```text
all-1(M) = 196883
all-2(M) = 393766
all-3(M) = 590649
(1,2,3)·M + 53 = all-2(M)
all-2(M) + 53 = (3,2,1)·M
(3,6,9)·M + 3×53 = all-6(M).
```

The uniform probes factor through total dimension.  The centred ordered probe detects the same invariant imbalance as the `3B` character, without pretending that the real weights `(1,2,3)` are roots of unity.

## The non-accidental Leech meaning of 196608

`DASHI/Moonshine/LeechWeightTwo196608BridgeExact.agda` gives a substantially stronger explanation than “`0x30000`”.

For the rank-24 Leech lattice VOA, the weight-two coordinate count is:

```text
196560  norm-four lattice exponentials
    24  h(-2)1 oscillators
   300  Sym²(h(-1)) oscillators
------
196884.
```

After choosing an orthonormal basis,

```text
300 = 24 diagonal quadratic coordinates + C(24,2)
    = 24 + 276.
```

Hence the exact subtotal is

```text
196608 = 196560 + 24 + 24,
```

and the completion is

```text
196884 = 196608 + 276,
196883 = 196608 + 276 - 1.
```

The `-1` removes the conformal line.  The diagonal/off-diagonal coordinate split depends on basis and is not claimed to be Monster-invariant, but the weight-two count is standard lattice-VOA mathematics.  This gives `196608` a real Moonshine-adjacent structural meaning while still not claiming that the Yang–Mills denominator was selected by the Leech VOA.

## The Heisenberg multiplicity ladder

`DASHI/Moonshine/Monster3BHeisenbergMultiplicityExact.agda` proves:

```text
3^6 = 729
90 = 12 + 78
729 × 12 = 8748
729 × 78 = 56862
729 × 90 = 65610
10 × 3^8 = 90 × 3^6 = 65610.
```

For an extraspecial group of order `3^(1+12)`, a nontrivial central character has faithful nonlinear degree `3^6`.  The highest-alpha representation target is therefore:

```text
Wζ restricted to 3^(1+12) ≅ Hζ^⊕90
Wζ² restricted to 3^(1+12) ≅ Hζ²^⊕90.
```

That theorem still requires the actual local-group identification or a certified character restriction; dimensions alone do not prove it.

The exhaustive executable model is:

```text
scripts/check_monster_3b_heisenberg_model.py
```

It checks:

- nondegeneracy and alternation of the standard symplectic form on `F₃⁶`;
- generator-level bilinearity;
- the Weyl relation on all 36 standard generator pairs and all 729 basis states;
- the extraspecial character-degree sum of squares;
- `729 × (12+78) = 65610`;
- the `10×3^8 = 90×3^6` overlap;
- the Leech weight-two identities above.

## Phase-preserving subgroup versus full normalizer

`DASHI/Moonshine/Monster3BPhaseTransportExact.agda` proves at the typed phase level that inversion fixes the invariant phase and exchanges `ζ` with `ζ²`.

Thus one nontrivial eigenspace is naturally stable under the subgroup fixing the selected generator, while the full normalizer may preserve only

```text
Wζ ⊕ Wζ².
```

This prevents silently treating `Wζ` as a module for an element that sends `g` to `g⁻¹`.

## E₈, Leech, 3⁸, and 3⁶

`DASHI/Moonshine/MonsterThreeLocalE8LeechBridgeExact.agda` reuses the repository’s existing E₈ and Leech benchmark data and separates:

- the rank-eight Euclidean E₈ lattice;
- the eight-dimensional quadratic space over `F₃` supporting `3^8.Ω⁻₈(3).2`;
- the rank-24 Leech lattice;
- the six-dimensional Lagrangian coordinate whose Schrödinger space has size `3^6`.

The sourced VOA literature places both

```text
3^(1+12).2.Suz:2
3^8.Ω⁻(8,3).2
```

inside the Moonshine construction.  They are distinct 3-local groups, but their candidate degree charts meet exactly at

```text
10×3^8 = 90×3^6 = 65610.
```

The file also reuses the existing E₈ root and Leech minimal-vector counts and records the standard arithmetic

```text
196560 = 240 × 3 × (1 + 16 + 16²).
```

## Function-first dashboards

The structural dashboard renders functions and orbit invariants, not decorative magnitude bars:

1. extraspecial quadratic-refinement phase kernels;
2. generator-to-invariant maps over all `729` states;
3. the complete `729×729` Heisenberg–Weyl phase portrait;
4. the full `729×(12+78)=65610` model carrier;
5. orbit-length strata under an explicit symplectic-model generator;
6. the actual CTblLib restriction sheet when the GAP certificate exists.

The central `3B` element is scalar on each nonlinear central-character sector.  It selects `ζ` versus `ζ²`; internal interference geometry must come from translations, modulations, Weil-type transformations, Suzuki-side operators, or genuine matrix coefficients of other normalizer generators.

## Exact remaining highest-alpha cut

The next proof-bearing steps are:

```text
1. observe a successful GAP/CTblLib CI certificate;
2. import the generated certificate into the cumulative Agda root;
3. identify the extraspecial kernel and its central 3B element in the certified local table;
4. prove finite Stone–von Neumann uniqueness in the repository’s representation layer;
5. construct Sζ = Hom_E(Hζ,Wζ) and prove dim Sζ = 90;
6. compute the actual inertia-group character on Sζ;
7. decide, from that character, whether Sζ ≅ S12 ⊕ S78;
8. import or construct genuine local-group generators and compare matrix traces with CTblLib;
9. only then seek an equivariant bridge from the existing 369/3^8/53 coordinate carriers.
```

The decisive mathematical endpoint is:

```text
Wζ restricted to E ≅ Hζ ⊗ Sζ,
E ≅ 3^(1+12),
dim Hζ = 729,
dim Sζ = 90.
```

The existing `10×3^9+53`, `3^11+3^9+53`, and reduced-53 carriers remain useful coordinate or associated-graded candidates.  They are not promoted to Monster branching rules until an explicit intertwiner, filtration, quotient, or character equality is proved.
