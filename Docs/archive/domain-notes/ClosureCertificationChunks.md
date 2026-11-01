# Closure Certification Chunks

Purpose: turn the current `L2` closure cone into a sequence of certifiable
chunks instead of relying only on one monolithic aggregate rerun.

This document does not change branch classification policy:

- `L0` / `L1` still decide theorem-owner and blocker status
- `L2` remains certification-only

## Aggregate Target

The full closure certification target is:

- `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`

That target remains the final aggregate check, but it should be treated as the
end of the sequence, not the only certification surface.

## Chunk Order

Use the current heavy closure cone as a staged certification ladder:

1. `transport-observable`
   - `DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`
   - `DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda`

2. `dynamics-gauge`
   - `DASHI/Physics/DashiDynamicsShiftInstance.agda`
   - `DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda`

3. `known-limits`
   - `DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda`
   - `DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda`

4. `atomic-gap`
   - `DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda`
   - `DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`

5. `closure-full`
   - `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`

## Intended Use

These chunks are for:

- offline certification
- decomposition work on the closure cone
- locating where the aggregate closure path becomes impractical

These chunks are not for:

- branch classification
- theorem promotion
- interactive inner-loop validation

## Result Interpretation

For each chunk, accept only:

- `clean`
- `error`
- `too_large`

Interpretation:

- `clean`: the chunk certifies under the current budget
- `error`: real type-level defect or missing import/threading issue
- `too_large`: the chunk needs more decomposition or a larger offline budget

## Runner

Use:

- `scripts/run_closure_full_check.sh`

Recommended modes:

- aggregate only:
  - `scripts/run_closure_full_check.sh`
- chunked:
  - `scripts/run_closure_full_check.sh --chunk transport-observable`
  - `scripts/run_closure_full_check.sh --chunk dynamics-gauge`
  - `scripts/run_closure_full_check.sh --chunk known-limits`
  - `scripts/run_closure_full_check.sh --chunk atomic-gap`
  - `scripts/run_closure_full_check.sh --chunk closure-full`
