# Yang–Mills highest-alpha Round 39 — redundancy-safe KKT projector and local constrained Green algebra

## Purpose

Round 39 repairs the exploratory Round-38 reduced-frame file and implements the redundancy-safe route demanded by the selected-background obstruction. The central compression is now exact:

```text
dS((I-P) w_(p,h)) = <lambda, L w_(p,h)>.
```

The projector spillover is therefore reduced to the literal multiplier defect `L w_(p,h)`, rather than estimated as a generic norm of a 3,072-coordinate repaired variation.

This tranche is finite algebra and proof architecture. It does **not** claim that the actual selected-background constraint matrix, its physical pseudoinverse, the sharp multiplier estimate, an interacting continuum measure, or an Osterwalder–Schrader Hamiltonian gap has been constructed.

## Sources

- Tadeusz Bałaban, *The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories*, DOI `10.1007/BF01229381`.
- Tadeusz Bałaban, *Averaging Operations for Lattice Gauge Theories*, DOI `10.1007/BF01211042`.
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.
- Roger Penrose, *A Generalized Inverse for Matrices*, DOI `10.1017/S0305004100030401`.
- Franco Brezzi, *On the Existence, Uniqueness and Approximation of Saddle-Point Problems Arising from Lagrangian Multipliers*; no DOI was assigned.
- Jean-Michel Combes and Lawrence Thomas, *Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger Operators*, DOI `10.1007/BF01646473`.
- Konrad Osterwalder and Robert Schrader, *Axioms for Euclidean Green's Functions* I and II, DOI `10.1007/BF01645738` and `10.1007/BF01608978`.

## Repaired reduced frame

`BalabanP33ReducedPhysicalHessianExact.agda` deletes the invalid attempt to choose an element of an arbitrary possibly-empty carrier. The replacement proves frame norm preservation by finite-sum congruence from an explicitly supplied finite coordinate enumeration and isometric-frame certificate. It constructs `H_phys = U* H U`, transports the quadratic floor, and derives both exact inverse laws from a rational matrix-inverse certificate.

## Redundancy-safe KKT projector

`BalabanP33FiniteKKTPseudoinverseProjectorExact.agda` keeps all multiplier rows. For

```text
K = L L*
P = I - L* K+ L
```

it proves constraint repair, `L P = 0`, `P²=P`, `P*=P`, that `P` fixes `ker L`, and that it kills `im L*`. Its authority theorem is the universal property:

```text
P v is the unique w such that
  L w = 0
  v-w lies in im L*.
```

The old two-sided Gram inverse is promoted into this pseudoinverse surface by `fullInverseToPseudoinverse`; it is not a competing public definition.

## Annihilator and KKT multiplier

`BalabanSelectedConstraintAnnihilatorKKTExact.agda` proves the finite-dimensional theorem

```text
ann(ker L) = im L*.
```

If the first-variation covector `g` annihilates every tangent in `ker L`, then `||P g||²=0`, hence `P g=0` and

```text
g = L* K+ L g.
```

The canonical multiplier is `K+ L g`; any two multipliers differ by an element of `ker L*`. The physical producer still required is `selectedFirstVariationAnnihilatesTangent`, derived from the actual Bałaban minimizer.

## Local extractor defect

`BalabanSelectedRawExtractorConstraintDefectExact.agda` forms the literal matrix

```text
L P_boundary(p)
```

and proves its action is `delta_(p,h)=L w_(p,h)`. A missed constraint row is exactly zero. Specializing the KKT equation gives

```text
dS((I-P) w_(p,h)) = <lambda, delta_(p,h)>.
```

The remaining locality theorem is the physical collar support of the actual selected constraint matrix.

## Cancellation and exact budget

Round 38 already puts raw localization and KKT repair into the same fifteen-atom ownership basis and removes exact-cancellation atoms before majorisation.

`BalabanP33SingletonBudgetFeasibilityExact.agda` makes the coefficient allocation exact:

```text
pair channel        =  9/18874368
singleton remainder = 55/18874368
correlated total    = 64/18874368 = rho/36.
```

A symbolic split is accepted only when `alpha,beta≥0` and `alpha+beta≤55/18874368`. The exact witness

```text
27/18874368 + 28/18874368 = 55/18874368
```

shows feasibility but is not asserted to be the physical split. A no-fit predicate exposes estimate families that necessarily overspend.

## Physical deep roles

Round 36 already proves the physical pair and deep lower bounds under the selected-background radius. `BalabanP33PhysicalFactorRoleDeepEnvelopeExact.agda` adds an exhaustive four-role dispatch:

```text
slot 0,1: positive orientation
slot 2,3: inverse orientation
```

with each placement's `value/first/second` selection. Every role dispatches to the existing physical selected-factor envelope, preventing omissions or double counting.

## Rational nonorthogonal frame

`BalabanP33NonorthogonalPhysicalFrameExact.agda` avoids rational orthonormalisation. For an injective rational frame `B` with invertible Gram matrix `G_B=B*B`, it constructs

```text
P_B = B G_B^-1 B*
H_B = B* H B
```

and transports coercivity as

```text
lambda <v,G_B v> <= <v,H_B v>.
```

The reduced inverse certificate has exact left/right laws. No square roots or algebraic extensions enter.

## Local KKT block and full-block tilt

An arbitrary nullspace frame can be spatially dense, so locality is retained in

```text
K_A = [ H_A  L_A* ]
      [ L_A   0   ].
```

`BalabanP33FiniteKKTBlockGreenAlgebraExact.agda` proves the projector/Hessian linearity. `BalabanP33FiniteKKTBlockGreenExact.agda` constructs

```text
r_g = L* (L L*)^-1 g
z   = G (f-H r_g)
v   = z+r_g
mu  = (L L*)^-1 L(f-Hv)
```

and proves pointwise `H v+L*mu=f` and `L v=g`.

`BalabanP33FiniteKKTBlockTiltExact.agda` tilts both state and multiplier blocks and splits the perturbation into exactly

```text
W H W^-1 - H
W L* W_M^-1 - L*
W_M L W^-1 - L.
```

It transports the finite KKT right inverse through conjugation. The remaining Combes–Thomas producer is the quantitative norm-smallness estimate for these three blocks.

## Covariant D4 boundary

`BalabanP33CovariantD4TransportCocycleBoundaryExact.agda` distinguishes strict slot permutation from actual background-dependent transport, which may obey

```text
T_g^A T_h^A = Gamma_A(g,h) T_(gh)^A.
```

Strict orbit reduction requires a trivial-cocycle certificate or invariance under the correction. Reflections cannot silently conflate slot reversal, inversion, quaternion conjugation, basepoint transport, and gauge repair.

## Gap authority boundary

`BalabanYangMillsGapAuthorityHierarchyExact.agda` separates four noncoercible types:

```text
FiniteBackgroundGaussianGap
UniformLatticeFluctuationGap
GaugeInvariantClusteringGap
OSReconstructedHamiltonianGap.
```

Promotion requires explicit uniformity, interacting RG/large-field control, limits, OS axioms, and spectral transfer. Round 39 is not a Clay mass-gap theorem.

## Exact remaining physical producers

1. `selectedBackgroundLinearizedConstraintMatrixExact` — differentiate the actual block average and gauge fixing and prove finite range.
2. `selectedBackgroundConstraintPseudoinverseCertificate` — identify redundancy and certify `K+` without deleting rows.
3. `selectedFirstVariationAnnihilatesTangent` — derive constrained criticality from the selected minimizer.
4. `selectedRawExtractorConstraintDefectAtomsExact` — compute the collar-supported atoms of `L_A w_(p,h)` and merge them with localization.
5. `rawLocalizationSpilloverUpper` and `selectedMultiplierDefectPairingUpper` — fit the surviving total inside `55/18874368`.
6. `selectedBackgroundPhysicalWLocal` and `selectedBackgroundHessianOneThirtySecond` — combine the new singleton estimate with the already physical pair/deep bounds to obtain

```text
H_A[h,h] >= 10739/196608 ||h||² >= 1/32 ||h||².
```

7. Instantiate the local KKT Green data and prove full-block Combes–Thomas smallness.

The all-scale interacting RG, large-field sector, thermodynamic/continuum limits, OS axioms, and reconstructed spectral gap remain later major programmes.

## Validation

```bash
AGDA_JOBS=1 bash scripts/check_yang_mills_clay_highest_alpha_round39.sh
```

The checker cascades through Round 37, rejects holes, postulates, unsafe escapes, trust primitives, imported theorem receipts, and the deleted invalid selector pattern, then invokes pinned Agda 2.9 on the cumulative Round-39 root.

No successful Agda-kernel or GitHub Actions result is claimed until observed.
