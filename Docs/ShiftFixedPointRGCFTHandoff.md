# Shift fixed-point RG/CFT handoff

## Scope

This tranche cross-pollinates the existing bounded shift dynamics with the
repo's balanced-ternary continuous-envelope lane. It now closes stronger finite
algebraic versions of the tangent, norm, semigroup, scaling, OPE, crossing,
correlation, and Ward lanes while keeping continuum/CFT promotion fail-closed.

```text
finite fixed-point classification
  -> finite pointed perturbation carrier
  -> exact induced derivative step
  -> Nat-indexed semigroup
  -> finite normed idempotent additive tangent algebra
  -> finite 2,1,0 scaling spectrum
  -> proof-relevant finite OPE coefficients
  -> finite exchange locality and crossing
  -> finite correlation/Ward analogues
  -> explicit analytic RG/CFT target records
  -> balanced-ternary continuous-envelope target
  -> still-open analytic instances
```

## Reused theorem surfaces

The implementation reuses rather than duplicates:

- `DashiDynamicsShiftInstance` for the exact shift step, held fixed point, and
  strict held-potential descent;
- `ShiftFixedPointPerturbationClassification` for the finite
  relevant/marginal/irrelevant classification;
- `ShiftPotentialQuadraticEnergy` and the collapse-depth/MDL chain for the
  existing descent evidence;
- `BalancedTernaryContinuousEnvelope` for the typed analytic interface needed
  by any later continuum depth/RG interpretation.

## New finite results

### Pointed tangent and semigroup

`ShiftFiniteTangentSemigroup.agda` introduces the three-element perturbation
carrier

```text
startPerturbation -> nextPerturbation -> zeroPerturbation -> zeroPerturbation
```

and proves the exact Nat-indexed composition law. Every orbit is absorbed at
zero from time two onward.

### Additive/normed tangent algebra

`ShiftFiniteNormedTangent.agda` promotes the existing fusion/join operation into
an exact idempotent commutative additive monoid on perturbations.

It proves:

- left and right zero laws;
- associativity and commutativity;
- idempotence;
- a triangle inequality for the existing finite rank norm;
- derivative preservation of addition;
- derivative non-expansiveness.

This is an actual finite normed additive structure, but not a vector or Banach
space: there are no additive inverses, scalar field, homogeneity theorem,
completeness theorem, or Fréchet derivative.

### Scaling spectrum

The finite scaling rank is inherited from the established held potential and
collapse depth:

```text
start : 2
next  : 1
held  : 0
```

These are exact finite ranks, not physical or anomalous scaling dimensions.

### Finite local OPE and crossing

`ShiftFiniteLocalOPECrossing.agda` adds explicit insertion sites and a
proof-relevant coefficient type

```text
OPECoefficient p q r = fusion p q == r
```

with a canonical `0/1` selection table. It proves:

- exchange locality from commutativity;
- crossing/associativity from the existing fusion theorem;
- exact equality of the two finite fusion channels.

This is a real finite algebraic OPE/crossing surface. It is not yet a continuum
field-theoretic OPE: there is no singular position dependence, analytic
coefficient function, convergence domain, conformal-block expansion, or QFT
reconstruction.

### Correlation / Ward analogues

The existing finite two-point correlation and held-insertion identities remain
attached. They are fixed-insertion finite identities, not stress-tensor or
conformal Ward theorems.

## Analytic target architecture

`FixedPointAnalyticRGTargets.agda` now names the exact stronger objects rather
than leaving them as prose:

- `AdditiveNormedTangent`;
- `FrechetLinearizedSemigroup`;
- `PhysicalScalingSpectrum`;
- `LocalOPECrossing`;
- `ContinuumRGControl`;
- `StressTensorConformalWard`;
- the integrated `FixedPointAnalyticRGCFTRoute`.

These are theorem-facing interfaces. No analytic instance is fabricated from
the three-point carrier.

## Continuum RG control

`ShiftFixedPointRGCFTHandoff.agda` routes the continuum obligation through the
existing `BalancedTernaryContinuousEnvelope` interface. That interface already
separates exact finite stream/truncation data from supplied analytic proofs of
convergence, weighted metric structure, cylinder continuity, first-difference
control, and injectivity.

The current tranche does not yet inhabit an analytic depth-kernel model or
prove that the finite semigroup intertwines a continuum renormalization flow.

## Remaining gates

The remaining work is now narrower:

1. upgrade the finite idempotent monoid to a vector/Banach tangent model;
2. inhabit Fréchet remainder, strong continuity, and generator-limit fields;
3. supply physically normalized and anomalous scaling dimensions;
4. supply analytic position-dependent OPE coefficients and conformal blocks;
5. inhabit the continuous-depth envelope with non-vacuous analytic predicates;
6. prove finite-to-depth RG intertwining and convergence;
7. construct a stress tensor and prove conformal Ward identities.

No continuum RG fixed point, conformal symmetry, or CFT is promoted by this
work.
