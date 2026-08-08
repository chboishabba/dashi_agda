# Monster 3B highest-alpha lane

This lane replaces dimension-only pictures with exact character-table computation, finite-Heisenberg identities, elementary-abelian subgroup strata, and typed boundaries around the still-unproved representation identifications.

## Primary sources

- R. W. Barraclough and R. A. Wilson, **“The Character Table of a Maximal Subgroup of the Monster”**, *LMS Journal of Computation and Mathematics* 10 (2007), 161–175. DOI `10.1112/S1461157000001352`.
- Robert A. Wilson, Peter Walsh, Richard A. Parker and Stephen Linton, **“A computer construction of the Monster”**, *Journal of Group Theory* 1 (1998), 307–337. DOI `10.1515/jgth.1998.023`.
- Hsian-Yang Chen, Ching Hung Lam and Hiroki Shimakura, **“Z₃-orbifold construction of the Moonshine vertex operator algebra and some maximal 3-local subgroups of the Monster”**, *Mathematische Zeitschrift* 288 (2018), 75–100. DOI `10.1007/s00209-017-1878-z`.
- Hiroki Shimakura, **“An E₈-approach to the moonshine vertex operator algebra”**, *Journal of the London Mathematical Society* 83 (2011), 493–516. DOI `10.1112/jlms/jdq078`.
- David J. Green and Ian J. Leary, **“Chern classes and extraspecial groups”**, *Manuscripta Mathematica* 88 (1995), 73–84. DOI `10.1007/BF02567806`.
- David J. Green and Ian J. Leary, **“The spectrum of the Chern subring”**, *Commentarii Mathematici Helvetici* 73 (1998), 406–426. DOI `10.1007/s000140050062`.
- John H. Conway and Simon P. Norton, **“Monstrous Moonshine”**, *Bulletin of the London Mathematical Society* 11 (1979), 308–339. DOI `10.1112/blms/11.3.308`.
- Igor B. Frenkel, James Lepowsky and Arne Meurman, **“Vertex Operator Algebras and the Monster”**, Academic Press, 1988. ISBN `978-0-12-267065-7`; no DOI asserted.

## One-command validation

```bash
bash scripts/check_monster_3b_normalizer_dashboard.sh
```

The checker always:

1. compiles the Python producers;
2. exhaustively validates the explicit finite-Heisenberg/Weyl model;
3. enumerates every one of the `11011` two-planes in `F₃⁶`;
4. generates function-first dashboards;
5. rejects postulates and unsafe trust escapes in the new Agda lane.

With GAP and CTblLib installed it additionally:

1. loads `CharacterTable("M")` and `CharacterTable("MN3B")`;
2. selects the unique Monster irreducible of degree `196883`;
3. restricts it through the stored `MN3B -> M` class fusion;
4. checks nonnegative integral multiplicities;
5. reconstructs the restricted character on every MN3B class;
6. identifies the size-two order-three source class fusing to Monster `3B`;
7. checks trace `53` and eigenspace multiplicities `(65663,65610,65610)`;
8. emits JSON and a generated Agda certificate.

The workflow `.github/workflows/monster-3b-normalizer.yml` installs GAP, CTblLib, Agda, the standard library, NumPy and Matplotlib, runs the checker, and uploads the certificates and plots.

## Exact `C₃` restriction target

The GAP producer is:

```text
scripts/monster_3b_normalizer_restriction.g
```

The generated certificate proves the arithmetic consequences of

```text
W restricted to C3
  = 1^65663 + zeta^65610 + zetaSquared^65610
  = 53·1 + 65610·Reg(C3).
```

Equivalently:

```text
65663 + 65610 + 65610 = 196883
65610 + 53 = 65663
3 × 65610 + 53 = 196883.
```

The GAP step, not a guessed constituent label, owns the actual normalizer restriction data.

## All-1, all-2, all-3, ordered 1-2-3, and 3-6-9

`DASHI/Moonshine/Monster3BCyclicFourierDyadicBridgeExact.agda` treats these as typed linear probes on the same multiplicity vector

```text
M = (65663,65610,65610).
```

Uniform probes see only dimension:

```text
(1,1,1)·M = 196883
(2,2,2)·M = 393766
(3,3,3)·M = 590649.
```

Ordered probes see the invariant imbalance:

```text
(1,2,3)·M + 53 = (2,2,2)·M
(2,2,2)·M + 53 = (3,2,1)·M
(3,6,9)·M + 3×53 = (6,6,6)·M.
```

This is the exact overlap with the 369 lane: the centred positional functional and the `C₃` Fourier character detect the same defect because the two nontrivial multiplicities agree. The real weights are not falsely identified with roots of unity.

## The stronger `196608` result

The previous “`0x30000` coincidence” has been replaced by a genuine lattice-VOA identity.

`DASHI/Moonshine/LeechWeightTwo196608BridgeExact.agda` proves the standard weight-two count for the rank-24 Leech lattice VOA:

```text
196560  norm-four lattice exponentials
    24  h(-2)1 oscillators
   300  Sym²(h(-1)) oscillators
------
196884.
```

After choosing an orthonormal coordinate basis,

```text
300 = 24 diagonal terms + C(24,2)
    = 24 + 276.
```

Therefore:

```text
196608 = 196560 + 24 + 24
196884 = 196608 + 276
196883 = 196608 + 275.
```

The final `-1` removes the conformal line. The diagonal/off-diagonal split is basis-dependent, so the `196608` subtotal is not promoted to a Monster-invariant submodule.

`DASHI/Moonshine/MonsterYangMills196608CrossLaneExact.agda` imports the actual Yang–Mills Wilson-budget object and proves:

```text
rho = 1/8192
sharpSixteenAtomBudget = 13/196608
196608 = 24 × 8192 = 3 × 2^16
196608 = Leech weight-two coordinate subtotal.
```

Thus the same integer is genuinely owned by both repository lanes. What remains unproved is a common selection mechanism, not the numerical overlap itself.

## Heisenberg multiplicity and the older `3^8` chart

`DASHI/Moonshine/Monster3BHeisenbergMultiplicityExact.agda` proves:

```text
3^6 = 729
90 = 12 + 78
729 × 12 = 8748
729 × 78 = 56862
729 × 90 = 65610
10 × 3^8 = 90 × 3^6 = 65610.
```

For either extraspecial type of order `3^(1+12)`, the character-degree multiset contains `3^12` linear characters and two nonlinear characters of degree `3^6`; both degree-square sums equal `3^13`. The plus/minus distinction therefore lives in group geometry, not character degrees.

The representation-theoretic target is:

```text
W_zeta restricted to E = H_zeta^⊕90
W_zetaSquared restricted to E = H_zetaSquared^⊕90
E = 3^(1+12).
```

The exact dimensional refactorization is proved. Actual isotypy still requires the certified local action or an equivalent character argument.

## E₈, Leech, `3^8`, and `3^6`

`DASHI/Moonshine/MonsterThreeLocalE8LeechBridgeExact.agda` reuses the repository’s existing E₈ and Leech benchmarks and keeps four roles distinct:

- rank-eight Euclidean E₈;
- the eight-dimensional quadratic space over `F₃` behind `3^8.Ω⁻₈(3).2`;
- the rank-24 Leech lattice;
- the six-dimensional Lagrangian coordinate whose Schrödinger space has `3^6` states.

The sourced VOA literature contains both 3-local shapes

```text
3^(1+12).2.Suz:2
3^8.Ω⁻₈(3).2.
```

They are not the same subgroup, but their proposed carrier charts meet exactly at `65610`. The file also records the standard E₈/Leech count

```text
196560 = 240 × 3 × (1 + 16 + 16²).
```

## Elementary abelian subgroup and Chern-subring inputs

`DASHI/Moonshine/Monster3BElementaryAbelianInvariantExact.agda` proves the exact two-plane strata of the six-dimensional symplectic carrier:

```text
[6 choose 2]_3 = 11011
isotropic two-planes = 3640
rank-two symplectic two-planes = 7371
3640 + 7371 = 11011.
```

The dashboard enumerates all `11011` RREF bases and maps each plane to:

- restricted alternating rank;
- zero counts of two declared quadratic probes;
- support coordinates and RREF weight;
- the commutator-rank input required by a future Chern restriction calculation.

No `kappa_r` class or Chern subring is fabricated from incidence data. Those remain a genuine cohomological construction.

## Phase transport

`DASHI/Moonshine/Monster3BPhaseTransportExact.agda` distinguishes the subgroup fixing a selected `3B` generator from the full cyclic normalizer. Generator inversion exchanges `zeta` and `zetaSquared`, so one nontrivial sector is naturally a module for the phase-preserving subgroup, while the full normalizer preserves their direct sum.

## Function-first dashboards

`scripts/monster_3b_structural_dashboard.py` now emits:

1. the exact extraspecial character-degree moment surface
   `M_n(s)=3^(2n)+2·3^(ns)` for both types and `n=1..6`;
2. the complete generator-to-invariant map for all `11011` elementary-abelian two-planes;
3. the full `729×729` Weyl phase function `arg(zeta^<x,b>)`;
4. an explicitly labelled model coupling on the full `729×(12+78)` carrier;
5. exact orbit-length strata under a declared invertible finite-field generator;
6. the certified CTblLib restriction-label function when GAP output exists.

No bar chart is part of this suite.

## Exact remaining highest-alpha cut

The completed lane now owns the arithmetic, Fourier probes, Leech subtotal, actual Yang–Mills denominator identity, finite-Heisenberg model, plus/minus degree comparison, elementary-abelian strata, phase transport, and executable normalizer restriction.

The irreducible mathematical frontier is:

```text
1. obtain a successful CTblLib workflow certificate;
2. identify the extraspecial kernel and selected central 3B element in the certified restriction;
3. prove or import finite Stone–von Neumann uniqueness in the representation layer;
4. construct S_zeta = Hom_E(H_zeta,W_zeta);
5. prove dim S_zeta = 90 and evaluation H_zeta tensor S_zeta -> W_zeta is an isomorphism;
6. compute the actual inertia-group character on S_zeta;
7. decide from that character whether S_zeta = S_12 direct-sum S_78;
8. import genuine local-group generators and match their traces to CTblLib;
9. only then construct an equivariant map from the existing 369, 3^8, and reduced-53 carriers.
```

The decisive endpoint remains:

```text
W_zeta restricted to E ≅ H_zeta tensor S_zeta,
E ≅ 3^(1+12),
dim H_zeta = 729,
dim S_zeta = 90.
```
