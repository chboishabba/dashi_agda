# MeasurementSurface Projection Contract

This note fixes the boundary for any future
`MeasurementSurface -> ΔState` interpretation.

Current status:

- no projection implementation exists,
- no `Δ` semantics are inferred from measurement surfaces by default,
- no theorem-side object may consume a projection result until this contract is
  made concrete for that lane.

## Purpose

The purpose of the projection contract is to prevent semantic leakage across
the empirical/formal boundary.

The current HEPData bridge stops at:

`dashitest -> canonical artifact -> MeasurementSurface`

That is intentional. A projection beyond `MeasurementSurface` is not parsing or
normalization. It is an interpretation step.

## Required contract shape

Any future projection must have the form:

`MeasurementSurface -> ProjectionResult`

where `ProjectionResult` is one of:

- `ok(delta_state, diagnostics)`
- `degraded(reason, diagnostics)`
- `rejected(reason, diagnostics)`

## Declared transform vocabulary

Any future projection must select one declared transform and emit the
corresponding diagnostics explicitly.

### `raw`

- meaning:
  use observed `y` as-is as the candidate signal
- preconditions:
  valid `x/y/cov` measurement surface and `metric_ready = true`
- required diagnostics:
  transform name, metric-geometry preservation flag, regularization flag,
  downstream-use declaration
- preserves metric geometry:
  yes
- requires regularization:
  no
- comparable group:
  `native`
- allowed downstream use:
  exploratory only unless explicitly promoted by a later lane

### `gradient`

- meaning:
  use local variation of `y` over `x` as the candidate signal
- preconditions:
  ordered `x`, finite spacing, valid covariance, declared derivative rule
- required diagnostics:
  transform name, derivative rule, metric-geometry preservation flag,
  regularization flag, downstream-use declaration
- preserves metric geometry:
  not automatically
- requires regularization:
  no
- comparable group:
  `derived`
- allowed downstream use:
  only with an explicit derivative/covariance propagation law

### `whitened`

- meaning:
  use covariance-normalized coordinates
- preconditions:
  full-rank covariance or explicitly declared regularization, plus recorded
  whitening operator
- required diagnostics:
  transform name, whitening operator, metric-geometry preservation flag,
  regularization flag, downstream-use declaration
- preserves metric geometry:
  no, it changes coordinate frame
- requires regularization:
  yes, whenever covariance is not directly invertible
- comparable group:
  `normalized`
- allowed downstream use:
  comparison only within the declared whitened frame

### `other-declared`

- meaning:
  any other transform, but only if explicitly named and documented
- preconditions:
  explicit transform declaration and explicit metric propagation law
- required diagnostics:
  transform name, declared meaning, metric-geometry preservation flag,
  regularization flag, downstream-use declaration
- preserves metric geometry:
  no default assumption
- requires regularization:
  no default assumption
- comparable group:
  `declared-other`
- allowed downstream use:
  none by default

## Minimum admissibility conditions

Before a projection can even be attempted, the following must be explicit:

1. semantic meaning of `delta`
2. semantic meaning of any `coarse_head`-like summary
3. covariance/metric propagation law
4. declared transform vocabulary with per-transform
   preconditions/meaning/diagnostics/downstream use
5. failure and abstention states

If any of those are missing, the correct outcome is rejection, not inference.

## Hard invariants

Any future implementation must preserve these invariants.

### 1. Metric law is explicit

If covariance is used as a metric carrier, the law must be stated explicitly.
No silent identity replacement is allowed.

### 2. No silent whitening

If whitening or any other metric transform is applied, it must be declared in
the result diagnostics and must match one declared vocabulary entry.

### 3. No covariance drop

Projection may not silently discard covariance information and still claim to
produce a metric-bearing downstream state.

### 4. Failure is first-class

Rank-deficient, ill-conditioned, or otherwise degraded surfaces may be
packaging-valid while still being projection-ineligible.

### 5. Claim boundary remains explicit

Projection output is theorem-adjacent at most. It does not become theorem-side
truth merely by existing.

## Current practical gate

The current report lane exposes:

- `metric_ready`
- `projection_eligible`

At present:

`projection_eligible := metric_ready`

That is intentionally narrow and conservative. It is a gate, not a projection.

## Code owner

The current contract stub lives in:

- [scripts/hepdata_projection_contract.py](/home/c/Documents/code/dashi_agda/scripts/hepdata_projection_contract.py)

This stub defines contract-only result types and precondition checks. It does
not implement any `MeasurementSurface -> ΔState` mapping.
