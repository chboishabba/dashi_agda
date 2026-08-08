# Monster 3B highest-alpha lane

This lane replaces dimension-only pictures with exact character-table computation, finite-Heisenberg generator proofs, elementary-abelian restriction data, and typed boundaries around the still-unproved Monster-module identifications.

## Primary sources

- R. W. Barraclough and R. A. Wilson, **“The Character Table of a Maximal Subgroup of the Monster”**, *LMS Journal of Computation and Mathematics* 10 (2007), 161–175. DOI `10.1112/S1461157000001352`.
- Robert A. Wilson, Peter Walsh, Richard A. Parker and Stephen Linton, **“A computer construction of the Monster”**, *Journal of Group Theory* 1 (1998), 307–337. DOI `10.1515/jgth.1998.023`.
- Hsian-Yang Chen, Ching Hung Lam and Hiroki Shimakura, **“Z₃-orbifold construction of the Moonshine vertex operator algebra and some maximal 3-local subgroups of the Monster”**, *Mathematische Zeitschrift* 288 (2018), 75–100. DOI `10.1007/s00209-017-1878-z`.
- Hiroki Shimakura, **“An E₈-approach to the moonshine vertex operator algebra”**, *Journal of the London Mathematical Society* 83 (2011), 493–516. DOI `10.1112/jlms/jdq078`.
- David J. Green and Ian J. Leary, **“Chern classes and extraspecial groups”**, *Manuscripta Mathematica* 88 (1995), 73–84. DOI `10.1007/BF02567806`.
- David J. Green and Ian J. Leary, **“The spectrum of the Chern subring”**, *Commentarii Mathematici Helvetici* 73 (1998), 406–426. DOI `10.1007/s000140050062`.
- John H. Conway and Simon P. Norton, **“Monstrous Moonshine”**, *Bulletin of the London Mathematical Society* 11 (1979), 308–339. DOI `10.1112/blms/11.3.308`.
- Igor B. Frenkel, James Lepowsky and Arne Meurman, **“Vertex Operator Algebras and the Monster”**, Academic Press, 1988. ISBN `978-0-12-267065-7`; no DOI asserted.

## Validation

```bash
bash scripts/check_monster_3b_normalizer_dashboard.sh
```

The checker always compiles the Python producers, validates the explicit finite-Heisenberg model, enumerates every one of the `11011` two-planes in the fixed Lagrangian `X=F₃⁶`, generates function-first dashboards, scans the Agda lane for trust escapes, and invokes the cumulative Agda root when Agda is installed.

With GAP and CTblLib it additionally restricts the unique degree-`196883` Monster character to `MN3B`, checks nonnegative integral multiplicities and classwise reconstruction, identifies the size-two order-three class fusing to Monster `3B`, verifies trace `53` and eigenspace multiplicities `(65663,65610,65610)`, and renders a generated Agda certificate.

The dedicated workflow `.github/workflows/monster-3b-normalizer.yml` installs GAP, CTblLib, Agda, the standard library, NumPy and Matplotlib and uploads all generated certificates and figures.

## Exact `C₃` restriction target

The executable producer is:

```text
scripts/monster_3b_normalizer_restriction.g
```

It certifies the data underlying

```text
W restricted to C3
  = 1^65663 + zeta^65610 + zetaSquared^65610
  = 53·1 + 65610·Reg(C3).
```

Thus:

```text
65663 + 65610 + 65610 = 196883
65610 + 53 = 65663
3 × 65610 + 53 = 196883.
```

Semantic names for `12`, `78`, `90`, or `3^6` are never inferred merely from a matching degree.

## All-1, all-2, all-3, ordered 1-2-3, and 3-6-9

`DASHI/Moonshine/Monster3BCyclicFourierDyadicBridgeExact.agda` treats these as typed linear probes on

```text
M = (65663,65610,65610).
```

Uniform probes see only total dimension:

```text
(1,1,1)·M = 196883
(2,2,2)·M = 393766
(3,3,3)·M = 590649.
```

Ordered probes detect the same invariant imbalance as the `3B` character:

```text
(1,2,3)·M + 53 = (2,2,2)·M
(2,2,2)·M + 53 = (3,2,1)·M
(3,6,9)·M + 3×53 = (6,6,6)·M.
```

This is the exact interaction with the 369 lane. The real positional weights are not identified with complex roots of unity; rather, their centred component and the `C₃` Fourier character both read the same defect because the two nontrivial multiplicities agree.

## The stronger meaning of `196608`

`DASHI/Moonshine/LeechWeightTwo196608BridgeExact.agda` proves the standard rank-24 lattice-VOA weight-two count:

```text
196560  norm-four Leech lattice exponentials
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
196884 = 196608 + 276.
```

The conformal vector lies in the diagonal `24`-dimensional quadratic sector, so the geometrically correct quotient is

```text
196883 = (196608 - 1) + 276
       = 196560 + 24 + 23 + 276.
```

The numerically equivalent identity `196883=196608+275` is retained only as arithmetic. No canonical `275`-dimensional off-diagonal subspace is asserted, and the diagonal/off-diagonal coordinate split is basis-dependent.

`DASHI/Moonshine/MonsterYangMills196608CrossLaneExact.agda` imports the actual Yang–Mills Wilson-budget object and proves:

```text
rho = 1/8192
sharpSixteenAtomBudget = 13/196608
196608 = 24 × 8192 = 3 × 2^16
196608 = the Leech weight-two coordinate subtotal.
```

So `196608` is a genuine shared arithmetic object in the two repository lanes, not merely a hexadecimal resemblance. A common dynamical selection theorem remains open.

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

For either extraspecial type of order `3^(1+12)`, the irreducible degree multiset has `3^12` linear characters and two nonlinear characters of degree `3^6`; both degree-square sums are `3^13`. The plus/minus distinction is therefore in group geometry, not character degrees.

`DASHI/Moonshine/Monster3BFiniteHeisenbergGeneratorsExact.agda` constructs the six translation and six modulation generators on the explicit six-trit Schrödinger carrier and proves all `36` standard Weyl exponent laws

```text
<b,x+a> = <b,a> + <b,x> in F3.
```

`DASHI/Moonshine/Monster3BFiniteHeisenbergPermutationExact.agda` proves constructive left and right inverse laws for each translation generator.

The actual local-module target remains:

```text
W_zeta restricted to E = H_zeta^⊕90
W_zetaSquared restricted to E = H_zetaSquared^⊕90
E = 3^(1+12).
```

## Correct Lagrangian and full-quotient geometry

The 729 Schrödinger basis states form

```text
X = F3^6.
```

The extraspecial quotient is

```text
E/Z(E) = X + X* = F3^12,
```

with the standard symplectic form. The Weyl phase is the perfect dual evaluation `zeta^<b,x>` for `x in X`, `b in X*`.

Every two-plane in the fixed Lagrangian `X` is automatically isotropic in the full quotient. `DASHI/Moonshine/Monster3BElementaryAbelianInvariantExact.agda` proves:

```text
[6 choose 2]_3 = 11011 fixed-Lagrangian two-planes.
```

Each plane `U` lifts with the centre to an elementary abelian subgroup of order `27`, and the 729-dimensional Schrödinger module restricts as

```text
81 copies of Reg(U),
9 × 81 = 729.
```

Separately, the full twelve-dimensional quotient has

```text
5883904390 total two-planes
1961279320 isotropic two-planes
3922625070 non-isotropic two-planes.
```

This corrects the earlier misuse of an arbitrary alternating form on `X` itself.

The dashboard maps all `11011` fixed-Lagrangian planes to their `15` Plücker coordinates, nonzero-vector Hamming-weight distributions, RREF pivots, and support sizes. These are genuine Grassmannian/coordinate invariants. No `kappa_r` class or Chern subring is fabricated; the future cohomological calculation must consume these subgroup restrictions explicitly.

## E₈, Leech, `3^8`, and `3^6`

`DASHI/Moonshine/MonsterThreeLocalE8LeechBridgeExact.agda` keeps four roles distinct:

- rank-eight Euclidean E₈;
- the eight-dimensional quadratic space over `F₃` behind `3^8.Ω⁻₈(3).2`;
- the rank-24 Leech lattice;
- the six-dimensional Lagrangian coordinate whose Schrödinger space has `3^6` states.

The sourced VOA constructions contain both `3^(1+12).2.Suz:2` and `3^8.Ω⁻₈(3).2`. They are different 3-local groups, while their candidate carrier dimensions meet exactly at `10×3^8=90×3^6=65610`. The file also records the E₈/Leech count

```text
196560 = 240 × 3 × (1 + 16 + 16²).
```

## Phase transport

`DASHI/Moonshine/Monster3BPhaseTransportExact.agda` distinguishes the subgroup fixing a selected `3B` generator from the full normalizer. Generator inversion exchanges `zeta` and `zetaSquared`; consequently one nontrivial eigenspace belongs naturally to the phase-preserving subgroup, while the full normalizer preserves their direct sum.

## Function-first dashboards

`scripts/monster_3b_structural_dashboard.py` emits no magnitude-only bar chart. It renders:

1. the exact extraspecial character-degree moment surface `M_n(s)=3^(2n)+2·3^(ns)` for both types and `n=1..6`;
2. the full Plücker/restriction-invariant function on all `11011` Lagrangian two-planes;
3. the complete `729×729` Weyl phase function `arg(zeta^<b,x>)` on `X*×X`;
4. an explicitly labelled model coupling on the full `729×(12+78)` carrier;
5. exact orbit-length strata under a declared invertible finite-field generator;
6. the certified CTblLib restriction-label function when GAP output exists.

## Exact remaining highest-alpha cut

The implemented lane owns the arithmetic and Fourier probes, the actual Yang–Mills/Leech `196608` identity, the explicit Weyl generator algebra, translation inverses, extraspecial degree data, fixed-Lagrangian subgroup restrictions, full symplectic two-plane counts, phase transport, and executable normalizer restriction.

The irreducible frontier is now:

```text
1. observe a successful CTblLib and Agda workflow certificate;
2. identify the extraspecial kernel and selected central 3B element in the certified restriction;
3. prove finite Stone–von Neumann uniqueness in the representation layer;
4. construct S_zeta = Hom_E(H_zeta,W_zeta);
5. prove dim S_zeta = 90 and H_zeta tensor S_zeta -> W_zeta is an isomorphism;
6. compute the actual inertia-group character on S_zeta;
7. decide whether S_zeta = S_12 direct-sum S_78;
8. import genuine local-group generators and match traces to CTblLib;
9. construct the actual kappa_r/Chern restrictions;
10. only then seek an equivariant map from the existing 369, 3^8, and reduced-53 carriers.
```

The decisive endpoint remains

```text
W_zeta restricted to E ≅ H_zeta tensor S_zeta,
E ≅ 3^(1+12),
dim H_zeta = 729,
dim S_zeta = 90.
```
