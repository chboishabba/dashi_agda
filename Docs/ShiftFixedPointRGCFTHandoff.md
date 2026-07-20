# Shift fixed-point RG/CFT handoff

## Scope

This tranche cross-pollinates the existing bounded shift dynamics with the
repo's balanced-ternary continuous-envelope lane. It closes finite precursor
surfaces for all six requested directions while keeping continuum and CFT
promotion fail-closed.

```text
finite fixed-point classification
  -> finite pointed perturbation carrier
  -> exact induced derivative step
  -> Nat-indexed iteration semigroup
  -> finite 2,1,0 scaling spectrum
  -> finite associative pointed fusion table
  -> held-insertion correlation/Ward analogues
  -> balanced-ternary continuous-envelope target
  -> still-open analytic RG/CFT gates
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

### Tangent perturbation carrier

`ShiftFiniteTangentSemigroup.agda` introduces a pointed three-element
perturbation carrier:

- `startPerturbation`;
- `nextPerturbation`;
- `zeroPerturbation` at held.

It is a finite tangent surrogate, not a vector space or smooth tangent bundle.

### Derivative / semigroup

The exact induced step is:

```text
startPerturbation -> nextPerturbation -> zeroPerturbation -> zeroPerturbation
```

Its Nat-indexed iteration satisfies an exact composition law and every orbit is
absorbed at zero from time two onward. This is a discrete semigroup theorem, not
an analytic generator theorem.

### Scaling spectrum

The finite scaling rank is inherited from the existing held potential and
collapse depth:

```text
start : 2
next  : 1
held  : 0
```

These are exact finite ranks, not physical or anomalous scaling dimensions.

### Fusion law

The finite perturbation carrier receives an associative pointed fusion table.
Zero is the unit and the more transient perturbation dominates. This is a
finite algebraic fusion surface, not an operator-product expansion: there are
no local fields, OPE coefficients, locality theorem, or crossing symmetry.

### Correlation / Ward analogues

A two-point finite correlation is built from the product of finite scaling
ranks. Held insertion is invariant under the exact step and has zero
correlation. These are finite fixed-insertion identities, not conformal Ward
identities and not a stress-tensor theorem.

## Continuum RG control

`ShiftFixedPointRGCFTHandoff.agda` routes the continuum obligation through the
existing `BalancedTernaryContinuousEnvelope` interface. That interface already
separates exact finite stream/truncation data from supplied analytic proofs of
convergence, weighted metric structure, cylinder continuity, first-difference
control, and injectivity.

The current tranche does not inhabit an analytic depth-kernel model or prove
that the finite shift semigroup is compatible with a continuum renormalization
flow.

## Remaining gates

A genuine fixed-point CFT theorem still requires:

1. additive or normed tangent structure;
2. an analytic derivative or semigroup generator;
3. physical scaling dimensions;
4. local OPE coefficients and crossing/associativity in the field-theoretic
   sense;
5. an inhabited continuous-depth envelope and RG compatibility across depth;
6. a stress tensor and conformal Ward identities.

No continuum RG fixed point, conformal symmetry, or CFT is promoted by this
work.
