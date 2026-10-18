# Substantive Millennium and graded-VOA cross-pollination

## Scope

This tranche is stacked on the Hurwitz–Hopf–Noether cross-pollination branch. It replaces the earlier relevance-only treatment of the remaining Millennium problems with native mathematical carriers, finite exact calculations, proof-bearing generic theorems, and explicit global theorem boundaries.

It covers:

- graded vertex operator algebras and the existing Monster/moonshine modules;
- the Riemann zeta/xi symmetry, zero, explicit-formula and Hilbert–Pólya surfaces;
- smooth projective varieties, Hodge decomposition, rational cycles and cycle classes;
- elliptic curves, local Frobenius factors, Mordell–Weil/Selmer/Sha and BSD;
- P, NP, polynomial reductions, Cook–Levin, circuits and GCT orbit obstructions;
- round-three-sphere Ricci flow and the geometrization-to-Poincaré implication.

No open Millennium problem is claimed solved. Poincaré is treated as a historically solved theorem whose full Perelman/Hamilton proof remains an external theorem boundary in this repository.


## 2026-09-28 live three-lane Clay recut

This document predates several later max-cut results.  For Hodge, BSD, and
P versus NP, the preferred theorem-search hierarchy is now the following.

### Hodge

**Official Clay-facing target**

For every smooth projective complex variety and every rational Hodge class,
construct a literal rational algebraic cycle whose cycle class reopens the
given class.

**Preferred reduction**

The live Hodge branch has already paid the primitive Lefschetz reduction and
the inverse-Lefschetz type firewall.  The remaining theorem is the primitive
cycle producer, exposed as

```text
PrimitiveAlgebraicLift
```

No general Lefschetz wrapper, Hodge decomposition identity, or observer
repackaging shortens this residual obligation.  Further Hodge work should only
be counted as progress when it constructs an algebraic cycle or strictly
reduces the unsupported primitive class.

### Birch--Swinnerton-Dyer

**Official Millennium rank target**

```text
analytic rank = Mordell--Weil rank
```

universally over rational elliptic curves.

The preferred prover-facing split is directional:

```text
Mordell--Weil rank <= analytic rank
analytic rank <= Mordell--Weil rank
```

The Lean BSD branch exposes these as independent universal theorem surfaces.
Ordinary Kummer/Selmer injection machinery naturally contributes toward the
first direction.  The reverse direction needs an independent zero-defect /
Selmer-excess / Sha-control theorem or a genuinely different universal
mechanism.

An unconstrained intermediate rank with equalities to both canonical ranks is
propositionally equivalent to the original BSD rank conjecture and therefore
does not shorten it.

**Refined BSD is a separate extension.**  Sha finiteness and the leading
coefficient identity are important refined-BSD targets but are not part of the
smallest mandatory handoff for the Millennium rank equality.  The live Lean
surface keeps these in a separate refined-extension status.

### P versus NP

**Official Clay-facing target**

```text
SAT not in P
```

under the repository's established NP-completeness/P-subset-NP background.

**Direct formal target**

```text
UniversalPolynomialSATDecisionFailure
```

That is: for every polynomial-time SAT decision candidate, produce a concrete
SAT decision error.  This is the preferred direct theorem surface.  The older
uniform observer/collision route is not the preferred public target: lossless
or identity observers show that a collision theorem of that generality is
false without a stronger coverage restriction.

The current self-reference/Q1 machinery is only a **candidate proof
mechanism** for reaching the direct failure theorem.  Its present max-cut is:

```text
candidate D
    |
    v
construct a candidate-dependent initial live state s_D
    |
    v
prove, without assuming a SAT error, that the first Q1 step must succeed
    |
    v
compare semantic residual width with the charged recursive measure
```

The critical semantic firewall is now:

```text
Q1OppositeSATTerminalSemantics
    <-> concrete SATDecisionFailure
```

for the current finite-code terminal construction.  Consequently terminal
opposite-SAT semantics must not be used as an innocent intermediate premise to
force first-step progress: doing so already supplies the lower-bound witness.

The current direct-DP route has additionally paid:

```text
literal exponential residual width for block equality
high width + small recursive measure -> no direct-DP run
high width + small recursive measure -> total constructor returns nothing
one successful direct-DP step -> one-node constant formula
```

Thus the only useful width experiment is on the **pre-first-step
candidate-coupled root**.

### Minimal prover handoff

The smallest current handoff for the three lanes is therefore:

```text
Hodge
  construct an algebraic cycle for every rational Hodge class;
  preferred reduction: solve the primitive algebraic lift.

BSD
  prove analytic rank = Mordell--Weil rank universally;
  preferred reduction: independently source both rank inequalities.
  Refined BSD remains separate.

P != NP
  for every polynomial-time SAT candidate, produce a concrete SAT
  decision failure (or prove an equivalent conventional all-machines
  lower bound).
```

Internal proof-search mechanisms should remain subordinate to these official
surfaces.  A mechanism is not itself a Clay theorem, and a theorem-equivalent
intermediate is not counted as a simplification merely because it has been
renamed.

## Graded VOA and moonshine

`GradedVertexOperatorAlgebraBoundary.agda` distinguishes a graded group representation from a VOA. It adds the missing data and laws:

```text
homogeneous spaces V_n,
vacuum in V_0,
conformal vector in V_2,
integer-indexed vertex modes,
translation operator,
lower truncation,
vacuum and creation identities,
translation covariance,
Jacobi identity,
Virasoro relations,
grading compatibility.
```

The existing `Moonshine.GradedRepresentation` remains the grade-wise action/trace owner. Given an exact trace law and the ordinary identity-endomorphism trace/dimension law, the new module proves

```text
traceCoefficient(identity,n) = dimensionScalar(n).
```

`MonsterGradedVOABridgeExact.agda` connects this surface to the existing Monster character-table, graded-trace and first-J-coefficient modules. It reuses

```text
196884 = 1 + 196883
```

without promoting that arithmetic identity into construction of `V^natural`.

Separate obligations remain for:

```text
construction of V^natural,
Aut(V^natural) = Monster,
rationality,
C2-cofiniteness,
modularity of graded characters,
McKay–Thompson coefficient identities,
genus zero.
```

## Riemann hypothesis

### Exact xi symmetry geometry

`RiemannXiSymmetryExact.agda` implements rational complex coordinates and the maps

```text
conjugation:       (sigma,t) |-> (sigma,-t),
functional:        (sigma,t) |-> (1-sigma,-t),
critical reflection:(sigma,t) |-> (1-sigma,t).
```

It proves:

```text
all three involution laws,
conjugation commutes with functional reflection,
critical reflection = conjugation after functional reflection,
critical-line points are fixed by critical reflection,
critical-reflection fixed points have real part 1/2,
functional and conjugation zero symmetry generates the zero quartet.
```

A Hilbert–Pólya candidate whose associated zero is

```text
1/2 + i lambda
```

has that represented zero on the critical line by construction.

### Analytic completed-zeta boundary

`RiemannCompletedZetaBoundary.agda` adds the actual analytic dependency surface:

```text
zeta,
Gamma/completion factor,
completed xi,
meromorphic continuation,
unique pole at 1,
Dirichlet series and Euler product regions,
functional equation,
conjugation law,
trivial and nontrivial zeros,
zero counting,
prime/zero explicit formula,
Weil positivity,
Hilbert–Pólya spectral completeness,
RH.
```

Supplying the functional equation and conjugation law automatically instantiates the exact zero-symmetry module. The analytic laws themselves are not inferred from the type definitions.

### Existing repository cross-pollination

`RiemannMaassMoonshineCrossPollinationExact.agda` connects the new surface to:

- `Analysis.AbelZeta` for the already recorded values at `0` and `-1`;
- the existing Maaß Fourier/residual/spectral-enclosure architecture;
- the graded-VOA character surface.

It keeps the following owners distinct:

```text
Abel-regularised special values,
Riemann meromorphic continuation,
Maaß Laplacian spectrum,
Selberg trace formula,
VOA modular characters,
Riemann prime/zero explicit formula,
Hilbert–Pólya spectrum.
```

The exact reusable implication is only:

```text
supplied self-adjoint spectral zero correspondence
=> represented zeros have real part 1/2.
```

Completeness of that correspondence remains the decisive missing theorem.

## Hodge conjecture

`HodgeDecompositionCycleClassExact.agda` adds:

```text
rational vector spaces,
smooth projective complex varieties,
singular/de Rham comparison,
H^(p,q) pieces,
Hodge decomposition,
complex conjugation,
rational algebraic cycles,
cycle-class maps,
rational Hodge classes.
```

For a supplied cycle-class map, the module proves that cycle classes are closed under rational sums and scalar multiples and live in the `(p,p)` piece.

The Hodge conjecture is represented exactly as the missing surjectivity statement:

```text
every rational Hodge class has an algebraic-cycle representative.
```

`ProjectiveLineHodgeDiamondExact.agda` records the exact finite table

```text
h00=1, h10=0, h01=0, h11=1,
b0=1, b1=0, b2=1,
```

and proves conjugation symmetry. A geometric-identification record is still required before the table is identified with an implemented cohomology construction.

`HodgeNoetherianVOACrossPollination.agda` separates:

```text
Noetherian finite presentation,
analytic Hodge decomposition,
algebraic cycle construction,
cycle-class surjectivity,
VOA/elliptic-genus modularity.
```

Noetherianity and VOA modularity do not manufacture the Hodge conjecture.

## BSD and elliptic curves

### Exact local arithmetic

`EllipticCurveFrobeniusExact.agda` defines short Weierstrass data and proves for

```text
E: y^2 = x^3 - x
```

that

```text
discriminant(E)=64.
```

For reduction at `p=5`, the exact affine fibre counts are

```text
1,1,2,2,1.
```

Therefore

```text
#E(F5)=7+1=8,
a5=5+1-8=-2,
P5(T)=1+2T+5T^2.
```

The finite Hasse row is carried by the explicit order proof

```text
|a5|^2 = 4 <= 20 = 4p.
```

### Global BSD boundary

`BirchSwinnertonDyerBoundary.agda` adds:

```text
abelian rational-point group,
finite generation and free rank,
torsion subgroup,
local Frobenius factors,
global Euler product and L-function,
analytic rank,
Selmer group,
Tate–Shafarevich group,
descent exact sequence,
period,
regulator,
Tamagawa product,
torsion order,
leading coefficient.
```

The rank conjecture is

```text
analyticRank = MordellWeilRank.
```

The leading-term conjecture is represented in denominator-cleared form:

```text
leadingCoefficient * torsionOrder^2
  = period * regulator * shaOrder * tamagawaProduct.
```

The module proves the symmetric rearrangement of this supplied equality but supplies no canonical conjecture inhabitant.

### Hodge/Frobenius cross-pollination

`EllipticCurveHodgeFrobeniusCrossPollination.agda` records the exact elliptic Hodge diamond

```text
1
1 1
1
```

and hence

```text
b0=1, b1=2, b2=1.
```

It separates:

```text
rational Weierstrass model,
complex Hodge realization,
finite-field Frobenius realization,
etale cohomology realization,
comparison across characteristics.
```

Matching dimensions do not establish the comparison theorem or compatibility of Frobenius characteristic polynomials.

## P versus NP and GCT

`PolynomialReductionExact.agda` defines:

```text
languages,
polynomial-time maps,
deterministic polynomial-time deciders,
polynomial verifiers and certificate bounds,
P,
NP,
polynomial many-one reductions,
NP-completeness,
P=NP.
```

It proves:

```text
identity reduction,
composition of polynomial reductions,
pullback of a P decider along a polynomial reduction,
an NP-complete language in P implies P=NP
  given the explicit P-subset-NP bridge.
```

`CookLevinCircuitGCTBoundary.agda` adds a concrete Boolean-formula evaluator and proves

```text
x OR NOT x
```

is a tautology and is satisfiable. It types the Cook–Levin tableau simulation, Boolean circuit families, circuit lower bounds and GCT orbit-closure machinery.

Using the existing Klein invariant theorem, it proves:

```text
invariant values differ
=> the two points are not in the same witnessed orbit.
```

Orbit-closure separation is stronger and remains a separate continuity/closure obligation. Classical `P versus NP` and algebraic `VP versus VNP` are distinct problem carriers.

## Poincaré and Ricci flow

`RoundThreeSphereRicciFlowExact.agda` implements the round unnormalised Ricci-flow model

```text
r^2(t)=r^2(0)-4t.
```

It proves:

```text
zero-time identity,
semigroup law,
constant decrement over an increment,
extinction at time T when r^2(0)=4T.
```

This does not establish Ricci-flow existence for arbitrary metrics.

`PoincareGeometrizationExactBoundary.agda` proves the exact logical composition:

```text
closed + connected + simply connected
-> spherical geometry          [geometrization input]
-> homeomorphic to S^3         [spherical classification input].
```

It reuses the repository's existing fail-closed Perelman authority socket and confirms that the geometrization authority remains unavailable locally.

`QuaternionS3PoincareCrossPollination.agda` connects the proof-bearing unit-quaternion carrier to a prospective smooth `S^3` point carrier, the round metric, Hopf circle action and Ricci-flow surface. The smooth-carrier equivalence and arbitrary-metric geometrization remain explicit fields.

## Cumulative validation

The focused root is:

```text
DASHI.Mathematics.CrossPollination.MillenniumSubstantiveCrossPollinationValidation
```

The whole-repository root is:

```text
DASHI.EverythingMillenniumSubstantiveCrossPollination
```

which imports the previous whole-repository Hurwitz–Hopf–Noether wrapper plus this tranche.

Run:

```bash
AGDA_JOBS=1 bash scripts/check_millennium_substantive_crosspollination.sh
```

The checker:

1. runs the complete checker for the preceding stacked tranche;
2. verifies every new source file exists;
3. rejects holes, postulates, unsafe pragmas, trust primitives and imported-theorem receipts in the new surface;
4. checks exact theorem, source-metadata and scope guards;
5. invokes pinned Agda 2.9 on the whole-repository wrapper.

No kernel or Actions success is claimed until an actual run is observed.
