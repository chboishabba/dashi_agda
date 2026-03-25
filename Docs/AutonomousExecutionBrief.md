# Autonomous Execution Brief

Date: `2026-03-25`
Phase: `physics-closure execution checklist`

## Purpose

This file exists to stop autonomous child runs from rediscovering repo context
that has already been settled. Read it before broad exploration.

## Active Objective

Advance the remaining canonical closure milestone:

- strengthen the constructive internals around the existing Lemma A / Lemma B
  signature-classification route
- keep canonical interfaces stable
- avoid drifting into generic docs cleanup or broad repo rediscovery

## Current Focus

Primary target surfaces:

- `DASHI/Geometry/CausalForcesLorentz31.agda`
- `DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda`
- `DASHI/Physics/Signature31IntrinsicShiftInstance.agda`
- `DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`
- `DASHI/Physics/Closure/ContractionForcesQuadraticStrong.agda`

Primary goal for this lane:

- replace weak/trivial constructive internals with stronger eliminator or
  classification witnesses where the public theorem interface already exists

## Constraints

- Do not treat setup, architecture, or audit as open work.
- Do not switch to broad documentation edits unless implementation actually
  changes and those docs must be synchronized.
- Do not use heavy aggregate validation as an inner-loop check.
- Do not use `PhysicsClosureValidationSummary.agda` as a routine target.
- Do not use full `Everything.agda` as a routine target.

## Preferred Validation

Use targeted Agda checks on touched canonical modules, for example:

- `agda -i . DASHI/Geometry/CausalForcesLorentz31.agda`
- `agda -i . DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda`
- `agda -i . DASHI/Physics/Signature31IntrinsicShiftInstance.agda`
- `agda -i . DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`

Only widen validation if the touched dependency chain requires it.

## Forbidden Or Bounded-Only Validation

- Do not run `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`
  as routine validation.
- Do not run full `DASHI/Everything.agda` as routine validation.
- Treat `DASHI/Physics/Closure/CanonicalStageC.agda` as bounded/checkpoint
  validation only, not a casual leaf check.
- If a targeted Agda command runs longer than expected without being an
  explicitly assigned checkpoint, stop it and report the risk instead of
  waiting indefinitely.

## Current Parallel Workstream Ownership

When multiple workers are active, keep file ownership disjoint:

- Signature / causal hardening:
  `CausalForcesLorentz31`, `Signature31FromIntrinsicShellForcing`,
  `Signature31Canonical`, `ContractionQuadraticToSignatureBridgeTheorem`,
  `ObservableResolutionInvarianceTheorem`, `PhysicsClosureFullInstance`
- Dynamics status / witness threading:
  `DASHI/HME/Trace.agda`, `DASHI/HME/Integration.agda`,
  `DynamicalClosureStatus`, `DynamicalClosureWitness`,
  `DynamicalClosureShiftInstance`
- Concrete constraint / algebraic closure:
  `CanonicalConstraintClosureWitness`, `PhysicsClosureFull`,
  `MinimalAlgebraicClosureTheorem`
- Known-limits consumer uplift:
  `CanonicalSpinDiracConsumer`, `CanonicalPropagationConsumer`,
  `CanonicalWaveGeometryConsumer`, `CanonicalLocalRecoveryConsumer`
- Later wave, not concurrent with the above unless reassigned:
  gauge-contract theorem work and Stage C grouped-consumer rewiring

## Operating Rules For Autonomous Children

1. Read `plan.md`, `status.md`, `status.json`, and this file.
2. Select one concrete theorem/code target from the focus list above.
3. Inspect only the files needed for that target.
4. Make a concrete implementation move before broad repo searching.
5. Run targeted validation on the touched module chain.
6. Update `status.md`, `devlog.md`, and `COMPACTIFIED_CONTEXT.md` only if real
   implementation progress occurred.

## Failure Pattern To Avoid

Bad loop:

- reread plan/status/context repeatedly
- run malformed `rg` searches
- rewrite docs without theorem/code advancement

Good loop:

- choose a single closure target
- inspect its local dependencies
- patch the theorem internals
- run targeted Agda checks
- record the concrete result
