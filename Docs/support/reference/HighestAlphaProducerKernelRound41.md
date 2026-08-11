# Highest-alpha Round 41 — physical producer kernel

Round 41 changes the unit of progress from completed reducers to explicit mathematical producers. It implements the common producer/reducer distinction, constructs the gauge-fixing component of the selected-background constraint operator, compresses Yang–Mills Gate I into one vertical plaquette witness, adds certified rational enclosure and slack accounting, corrects the Mosco gap-transfer direction, and attacks the Navier–Stokes HH-bad scale obstruction directly.

## Producer maturity is now a type, not a Boolean

`PhysicalProducerMaturityExact.agda` distinguishes:

```text
reducerComplete
certificateSchemaComplete
syntheticFixtureComplete
physicalProducerComplete
scaleUniformProducerComplete
continuumProducerComplete
```

A `PhysicalProducer Object Admissible` contains an actual object and a proof that it satisfies the admissibility predicate. `SameCarrierSameObject` records a literal

```text
source -> intermediate -> output
```

chain together with two explicit representation relations. Both transformations must preserve their relation for every input, and the selected intermediate and output must be the literal computed values. This prevents an extensionally convenient but physically unrelated object from being substituted between the producer and reducer.

## Yang–Mills: the literal gauge-fixing component of `L_A`

The repository already had the covariant backward-divergence derivative

```text
D F_A[h](x)
  = sum_mu (h_mu(x)
    - Ad_(U_mu(x-mu)^-1) h_mu(x-mu)).
```

Round 41 turns this derivative into an actual rectangular KKT matrix rather than accepting a matrix from a caller. `BalabanFiniteLinearFunctionalCoordinatesExact.agda` proves, on any concrete finite coordinate carrier,

```text
F(v) = sum_j F(e_j) v_j
```

for every explicitly linear functional `F`. `BalabanSelectedBackgroundGaugeConstraintMatrixExact.agda` then proves zero, additivity, scalar compatibility and pointwise congruence of the literal quaternionic gauge derivative, defines

```text
selectedBackgroundGaugeConstraintMatrix A r c
  = D F_A[e_c](r),
```

and proves

```text
selectedBackgroundGaugeConstraintMatrixApplyExact :
  (L_gauge(A) v)(r)
  = D F_A[decode(v)](r).
```

`BalabanSelectedBackgroundGaugeConstraintStencilExact.agda` proves the exact support theorem: a row based at `x` sees only a positive bond based at `x` or the positive bond of direction `mu` based at `x-mu`. The adjoint transport may mix Lie coordinates but cannot enlarge the spatial stencil. Thus every entry outside that stencil is exactly zero before majorisation.

`BalabanSelectedBackgroundGaugeGramFiniteRangeExact.agda` composes this matrix with its transpose. If two gauge rows have disjoint literal stencils, every summand in their Gram entry vanishes and

```text
selectedBackgroundGaugeGramOutsideRangeZero :
  disjointStencil(left,right)
  -> (L_gauge L_gauge*)(left,right) = 0.
```

This closes the gauge-only Gram finite-range identity structurally, before any Combes–Thomas norm estimate.

This closes the literal gauge-fixing component of `L_A`. It does not silently identify that component with the missing derivative of the block-average constraint. The next Yang–Mills matrix task is to construct that block-average row family and combine it with the now-concrete gauge rows on one multiplier carrier.

## Yang–Mills: one vertical selected-plaquette witness

The new object is

```text
LiteralSelectedPlaquetteWitness background bondField plaquette
```

It owns, in one record:

- the multiplier carrier;
- the literal constraint matrix through `pseudoData`;
- the Gram Moore–Penrose pseudoinverse;
- the first-variation covector;
- the literal source/defect atom authority;
- the selected local variation;
- Euler–Lagrange stationarity;
- the corrected projected-variation identity;
- exact cancellation;
- all four surviving owner estimates.

The theorem

```text
literalSelectedPlaquetteWitnessToCorrelatedExtractionData
```

converts this one object to the Round-40 reducer. A family of such witnesses gives the physical selector without accepting a free residual family or scalar equality.

This is the correct implementation target for the remaining finite Gate-I work. The record is not itself a claim that the complete physical selected-background witness has already been constructed.

## Exact Yang–Mills robustness budget

The owner allowance is

```text
55 / 18874368
```

and the new explicit slack is

```text
Delta_YM
  = 55 / 18874368
    - (c_loc + c_transport + c_near + c_far).
```

`CorrelatedOwnerBoundsWithSlack` accepts a coefficient total below the allowance rather than requiring exact equality. `slackCompletesLegacyOwnerBudget` allocates unused slack to the far coefficient only when calling the legacy reducer. Because the charge and `Delta_YM` are nonnegative, the enlarged coefficient is still a sound upper bound.

`CertifiedCorrelatedOwnerEnclosures` supplies the interval-analysis route. Each physical owner may be established by a rational centre and radius together with an exact enclosure proof. The theorem

```text
certifiedEnclosuresToOwnerBounds
```

turns those four enclosures into the slack-preserving physical budget. This is the weakest exact certificate needed by the current scalar reducer; it does not require printing closed-form entries of every inverse matrix.

## Mosco correction: recovery, not liminf alone, transfers a gap

Round 41 proves the exact order chain

```text
m ||u||^2
  <= m ||u_n||^2
  <= Q_n(u_n)
  <= Q_infinity(u).
```

The final inequality is a recovery/Mosco-upper estimate. A liminf statement alone has the opposite order:

```text
Q_infinity(u) <= liminf Q_n(u_n).
```

It cannot exclude a downward drop of the limiting form. The file contains a literal rational countermodel with finite norm and finite energy both equal to one, but limiting energy zero. The desired limiting gap would require `1 <= 0`.

Therefore the weaker continuum route should be stated as:

```text
common carrier
-> vacuum-sector-stable recovery sequence
-> uniform finite form gap
-> limiting form gap
-> spectral identification.
```

Trace-norm convergence of transfer operators remains sufficient, but it is not the only possible route and should not be demanded unless the constructive input actually supplies it.

## Navier–Stokes finite same-object layer

`NSGalerkinSameObjectExact.agda` no longer accepts an arbitrary coefficient function. A `CanonicalGalerkinState` contains a representation-preserving chain from the physical source to an encoded state and then to the coefficient function consumed by the Galerkin vector field. The requested seams are literal theorems of that same output:

```text
velocityAtPositiveExact
velocityAtNegativeExact
retainedModesExact
actualTriadCancellationExact
```

The finite cyclic triad cancellation is proved by rational ring normalization. This is Layer F: it ensures later estimates concern the actual generated Galerkin object. It is not the cutoff-uniform regularity estimate.

## Navier–Stokes HH-bad falsification target

The raw half-kernel/two-derivative route leaves

```text
rawHHBadCost(q) = 2 * 2^q.
```

Round 41 proves:

```text
rawHHBadCost(q+1) = 2 * rawHHBadCost(q),
```

and the cost already exceeds `1/64` at shell zero. Thus raw Bernstein and the parabolic half-kernel cannot supply a cutoff-uniform viscosity coefficient.

The exact compensating gain for a target coefficient `eta` is

```text
requiredHHBadGain(eta,q) = (eta / 2) * 2^(-q).
```

The calibration theorem proves

```text
requiredHHBadGain(eta,q) * rawHHBadCost(q) = eta.
```

Consequently `physicalHHBadEstimateFromScaleGain` closes the owner only after a physical theorem supplies that gain. The source must be explicit: geometric alignment, short-time support, dissipation-range localization, intermittency, excursion-count suppression, or signed cancellation. An uncontrolled BKM/Serrin quantity cannot be used as the source.

## Anti-circularity is proof-carrying

`NSAdmissibleRemainderGrammarExact.agda` now has a `RemainderSourceAuthority` with an actual source type, numerical interpretation, dependency relation and four proof predicates:

```text
InitialDataBounded
KnownTimeIntegralFinite
LowerOrderControlled
DissipationAbsorbable
```

Each admissible leaf contains its source and the applicable proof. The authority must prove that each certificate excludes all three forbidden dependencies:

```text
targetCriticalSupremum
uncontrolledBKMIntegral
uncontrolledSerrinNorm
```

Finite sums remain available, but an unrestricted rational can no longer be relabelled as a known integral or lower-order term and passed through the fold.

## Exact nine-owner strict absorption

For the nine physical owner coefficients, Round 41 defines

```text
Delta_NS = 1 - sum_i eta_i
```

and requires `Delta_NS > 0`. The theorem

```text
nineOwnerAbsorptionWithSlack
```

proves

```text
sum_i P_i + Delta_NS * D <= D.
```

The remaining Navier–Stokes frontier is therefore not terminal absorption arithmetic. It is the construction of the nine cutoff-uniform physical owner inequalities, beginning with the HH-bad gain theorem.

## Exact live producer obligations

### Yang–Mills

1. Construct the derivative of the actual selected block average and combine it with the now-literal gauge-fixing component to form the complete finite-range `L_A`.
2. Supply an exact or certified-rank-stable pseudoinverse for `K_A = L_A L_A*` on that same combined object.
3. Derive tangent annihilation from the actual selected minimizer.
4. Construct the literal source and defect atoms for each physical plaquette.
5. Prove exact cancellation and four certified owner enclosures with `Delta_YM >= 0`, preferably `Delta_YM > 0`.
6. Instantiate `LiteralSelectedPlaquetteFamily` and obtain the existing `1/32` Hessian floor.

### Navier–Stokes

1. Instantiate the representation-preserving Galerkin source/encoding relations for the repository's existing physical finite carrier.
2. Prove a concrete mechanism yielding at least `(eta/2) 2^(-q)` in HH-bad.
3. Prove the commutator and tail owners with the same cutoff-uniform discipline.
4. Construct all remaining owner inequalities with proof-carrying admissible remainders only.
5. Produce a packet with explicit `Delta_NS > 0` before compactness and restart.

Round 41 does not claim either Clay problem is solved. It removes two misleading shortcuts—equality-only budget accounting and Mosco-liminf-only gap transport—while closing one literal physical matrix component and making the hardest next producer in each lane exact and falsifiable.
