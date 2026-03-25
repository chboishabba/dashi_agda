# Agda Validation Targets

Purpose: record which Agda modules are safe for routine targeted validation and
which ones should be avoided in normal loops because they are known to be
runtime-heavy or aggregate too much of the closure surface at once.

## Safe Routine Targets

These are the preferred modules for focused validation while working on the
canonical closure spine:

- `DASHI/Geometry/CausalForcesLorentz31.agda`
- `DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda`
- `DASHI/Physics/Signature31IntrinsicShiftInstance.agda`
- `DASHI/Physics/Signature31FromShiftOrbitProfile.agda`
- `DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`
- `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`
- `DASHI/Physics/CliffordEvenLiftBridge.agda`
- `DASHI/Physics/Closure/CliffordToEvenWaveLiftBridgeTheorem.agda`
- `DASHI/Physics/Closure/CanonicalContractionToCliffordBridgeTheorem.agda`
- `DASHI/Physics/Closure/KnownLimitsQFTBridgeTheorem.agda`
- `DASHI/Physics/Closure/Canonical/LocalProgramBundle.agda`
- `DASHI/Physics/Closure/Canonical/Ladder.agda`
- `DASHI/Physics/Closure/PhysicsClosureSummary.agda`

Use these for routine theorem-edit loops and targeted bridge checks.

## Heavy / Avoid In Routine Loops

These should not be part of normal rapid validation passes:

- `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`
- `DASHI/Everything.agda`

Reason:

- `PhysicsClosureValidationSummary.agda` is the known heavy aggregate closure
  summary and currently remains outside routine validation policy.
- `Everything.agda` is the authoritative top-level route, but bounded local
  checks currently time out because it eventually pulls the heavy validation
  summary path.

## Bounded-Only Target

- `DASHI/Physics/Closure/CanonicalStageC.agda`

This module is not banned, but it is heavy enough that bounded runs can still
time out. Use it as a checkpoint module, not as the default inner-loop target.

## Hygiene Script Policy

- `scripts/run_closure_hygiene.py`
- `scripts/run_closure_hygiene.sh`

These now skip learned `heavy` and `aggregator` tasks by default. Use
`--include-heavy` only for deliberate aggregate validation runs with a larger
runtime budget.

## Practical Rule

Default inner loop:

1. run one or two canonical bridge modules directly
2. run `PhysicsClosureSummary.agda` if you need a broader canonical surface
3. avoid `PhysicsClosureValidationSummary.agda` unless you are explicitly doing
   a long-budget validation pass
4. treat `Everything.agda` as an occasional bounded checkpoint, not a routine
   target
