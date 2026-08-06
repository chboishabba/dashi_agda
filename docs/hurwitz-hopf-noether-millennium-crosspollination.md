# Hurwitz–Hopf–Noether Millennium cross-pollination

## Scope

This tranche implements the algebra/symmetry/topology backbone requested in the supplied brief while preserving the repository's existing authority boundaries.

It is stacked on the current Yang–Mills Round 30 branch because that line already contains the exact rational quaternion carrier, Wilson plaquette algebra, SU(2) trace normalization, and the fixed-lattice-versus-continuum mass-gap gate hierarchy. It does not supersede the separate Navier–Stokes Round 20 branch. Instead, it adds NS-facing structural interfaces that can later be merged or rebased onto that physical-audit line.

The locally checked surface is:

```text
exact rational complex algebra
-> one Cayley–Dickson doubling
-> existing rational quaternion multiplication
-> conjugation and multiplicative norm
-> quaternionic Hopf radius identity

finite law profiles / dimension candidates
-> Frobenius candidate subset of Hurwitz candidates
-> Hopf-invariant-one dimension coincidence

Klein group action
-> invariant observable
-> constant on witnessed orbit

Noether rate + dissipation = residual
-> coupled cancellation
-> distinct ordinary / covariant / dissipative conservation kinds

YM: shared quaternion carrier -> SU(2) trace -> Hopf/instanton gate
NS: critical scaling + defect ledger + Hopf/helicity/continuation gate
```

No historical classification theorem, bundle theorem, instanton theorem, PDE regularity theorem, continuum reconstruction theorem, or Millennium solution is imported merely by citation.

## Exact algebraic implementation

### Cayley–Dickson to the existing quaternion carrier

`CayleyDicksonRationalComplexQuaternionExact.agda` defines rational complex arithmetic and the doubling convention

```text
(a,b)(c,d) = (ac - conjugate(d)b, da + b conjugate(c)).
```

It proves coordinate-by-coordinate that the resulting four rational coordinates are exactly the multiplication already implemented in

```text
BalabanP33RationalQuaternionWilsonSecondVariationExact.RationalQuaternion.
```

It also proves:

```text
conjugate(conjugate(q)) = q,
conjugate(pq) = conjugate(q) conjugate(p),
N(pq) = N(p)N(q),
N(p)=N(a)+N(b)
```

for the concrete rational complex/quaternion carriers.

This is the central repository reuse: the quaternion algebra used for Wilson-Hessian mathematics is now also the concrete Cayley–Dickson and Hopf carrier.

### Hurwitz/Frobenius law profiles

`HurwitzFrobeniusLawProfileExact.agda` records the finite table for

```text
R, C, H, O, sedenions
```

with commutativity, associativity, alternativity, flexibility, norm composition, and division flags. It proves finite candidate-table facts such as:

```text
Frobenius candidate => Hurwitz candidate,
H is in both tables,
O separates the tables,
sedenions are in neither.
```

Indexed types expose dimensions

```text
Frobenius: 1,2,4
Hurwitz:   1,2,4,8.
```

These are finite checked candidate surfaces, not a proof that the lists classify all finite-dimensional real division/composition algebras.

### Hopf dimension and radius mathematics

`HopfInvariantOneDimensionGateExact.agda` proves the finite type-level correspondence

```text
HurwitzDimension n <-> HopfInvariantOneDimension n
```

for `n = 1,2,4,8`, while explicitly not claiming Adams's theorem.

`QuaternionHopfRadiusExact.agda` implements

```text
H(a,b) = (2 a conjugate(b), N(a)-N(b))
```

and proves

```text
N(2 a conjugate(b)) + (N(a)-N(b))^2
  = (N(a)+N(b))^2.
```

Thus a rational pair with `N(a)+N(b)=1` maps to the target unit quadric. Local triviality, fibre identification, smooth sphere structure, characteristic classes, and instanton geometry remain separate obligations.

## Klein and Noether

### Klein invariant surface

`KleinGroupActionInvariantExact.agda` defines a generic group action and a rational observable invariant under the action. It proves the observable is constant on every explicitly witnessed orbit, including composed orbit witnesses.

This is reused directly by `YangMillsKleinNoetherGaugeInvariantBridgeExact.agda`: a gauge-invariant rational action has equal values on gauge-related configurations.

### Noether symmetry versus Noetherianity

Two modules keep the meanings separate:

- `NoetherDissipationDefectExact.agda` handles the variational/conservation ledger;
- `NoetherianityMeaningSeparationExact.agda` handles ascending-chain and finite-generation obligation surfaces.

The defect ledger proves exact algebra such as

```text
rate = -dissipation + residual
=> rate + dissipation = residual
```

and the coupled cancellation

```text
E' + D = N + R_E
S'     = -N + R_S
-----------------
(E'+S') + D = R_E + R_S.
```

Ordinary conservation, covariant conservation, and dissipative defect laws are distinct constructors.

## Yang–Mills cross-pollination

`YangMillsHurwitzHopfStructuralGateExact.agda` proves that the Hopf/Cayley–Dickson quaternion carrier is definitionally the same carrier used by the current SU(2) lattice action. It reuses:

```text
Re Tr(1) = 2,
N(pq)=N(p)N(q),
quaternionic Hopf radius identity.
```

It then separates the stages:

```text
rational quaternion ring
-> SU(2) normalization
-> Hopf radius identity
-> principal SU(2) bundle over S4
-> BPST self-dual connection
-> integral second Chern sector
-> interacting Euclidean measure
-> continuum OS reconstruction
-> positive Hamiltonian mass gap.
```

The new gate also reuses the existing theorem that fixed-lattice exponential clustering is not the reconstructed continuum Hamiltonian gap.

`YangMillsKleinNoetherGaugeInvariantBridgeExact.agda` separately connects:

```text
finite gauge orbit invariance
-> infinitesimal Noether obligation
-> covariant Bianchi / Euler–Lagrange obligation
```

without promoting any of them into reflection positivity or spectral-gap control.

## Navier–Stokes cross-pollination

`NavierStokesKleinCriticalScalingExact.agda` checks the three-dimensional exponent arithmetic for

```text
u_lambda(x,t) = lambda u(lambda x,lambda^2 t).
```

It proves exact criticality for:

```text
L^3_x,
L^infinity_t L^3_x,
L^2_t L^infinity_x,
L^4_t L^6_x,
pressure L^(3/2)_x.
```

`NavierStokesHopfNoetherContinuationGateExact.agda` reuses the Noether-defect cancellation and distinguishes:

```text
Hopf radius identity
!= helicity/linking identification
!= vortex-stretching estimate
!= BKM integral control
!= critical continuation
!= global smoothness.
```

The two genuine missing bridge records are:

1. physical Hopf/helicity/linking hypotheses;
2. analytic pressure/Biot–Savart/stretching/time-integrability/continuation control.

This provides a clean future merge surface for the live directional high-high, bad-time residence, and critical continuation work on the NS Round 20 branch.

## Other Millennium problems

`MillenniumProblemStructuralRelevanceGateExact.agda` records a finite dependency classifier rather than a proof claim. It distinguishes foundational, direct-special-case, indirect, and absent relevance across:

- Yang–Mills mass gap;
- Navier–Stokes regularity;
- Hodge;
- Birch and Swinnerton-Dyer;
- Riemann hypothesis;
- P versus NP;
- the historical Poincaré problem.

Most importantly, it separates:

```text
Frobenius real division-algebra theorem
!= arithmetic Frobenius endomorphism.
```

BSD and arithmetic-geometric Hodge contexts use the second much more directly; the real division-algebra theorem is only indirect/example-level infrastructure there.

## Source metadata recorded in Agda

Headers record authors, titles, and identifiers for:

- John C. Baez, *The Octonions*, DOI `10.1090/S0273-0979-01-00934-X`;
- Aleksandra Galecka, *A Proof of the Hurwitz Theorem About Composition Algebras*, DOI `10.24917/20809751.13.4`;
- Adolf Hurwitz, *Über die Komposition der quadratischen Formen*, DOI `10.1007/BF01448439`;
- Matej Bresar and Victor S. Shulman, *On, around, and beyond Frobenius' theorem on division algebras*, DOI `10.1080/03081087.2020.1761281`;
- Heinz Hopf, *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*, DOI `10.1007/BF01457962`;
- J. F. Adams, *On the Non-Existence of Elements of Hopf Invariant One*, DOI `10.2307/1970147`;
- Emmy Noether, *Idealtheorie in Ringbereichen*, DOI `10.1007/BF01464225`;
- Emmy Noether, *Invariante Variationsprobleme*, original with no DOI; Tavel translation DOI `10.48550/arXiv.physics/0503066`;
- David Eisenbud, *Commutative Algebra: with a View Toward Algebraic Geometry*, DOI `10.1007/978-1-4612-5350-1`;
- A. A. Belavin, A. M. Polyakov, A. S. Schwartz and Yu. S. Tyupkin, *Pseudoparticle Solutions of the Yang–Mills Equations*, DOI `10.1016/0370-2693(75)90163-X`;
- H. K. Moffatt, *The degree of knottedness of tangled vortex lines*, DOI `10.1017/S0022112069000991`;
- Vladimir I. Arnold and Boris A. Khesin, *Topological Methods in Hydrodynamics*, second edition, DOI `10.1007/978-3-030-74278-2`;
- James Serrin, *On the Interior Regularity of Weak Solutions of the Navier–Stokes Equations*, DOI `10.1007/BF00253344`;
- J. T. Beale, T. Kato and A. Majda, DOI `10.1007/BF01212349`;
- Kenneth G. Wilson, DOI `10.1103/PhysRevD.10.2445`;
- the official Clay problem descriptions, with no DOI asserted.

## Validation

```bash
AGDA_JOBS=1 bash scripts/check_hurwitz_hopf_noether_millennium_crosspollination.sh
```

The checker cascades through the full Yang–Mills Round 30 checker, rejects holes, postulates, trust primitives, unsafe escapes and theorem-receipt shortcuts, verifies theorem/source/scope guards, then invokes the pinned Agda 2.9 cumulative root.
