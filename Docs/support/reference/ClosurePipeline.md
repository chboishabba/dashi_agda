# Closure Pipeline (Canonical Map)

## Purpose

This document defines the single authoritative theorem chain for Stage C
closure claims. New proof work should extend this chain or be explicitly
labeled as alternative/validation/experimental.

## Canonical Chain

Stage C canonical closure route (execution order):

1. `DASHI/Geometry/ProjectionDefect.agda`
2. `DASHI/Geometry/ProjectionDefectSplitForcesParallelogram.agda`
3. `DASHI/Geometry/ProjectionDefectToParallelogram.agda`
4. `DASHI/Geometry/QuadraticForm.agda`
5. `DASHI/Physics/Closure/ContractionForcesQuadraticStrong.agda`
6. `DASHI/Physics/Closure/ContractionForcesQuadraticTheorem.agda`
7. `DASHI/Geometry/CausalForcesLorentz31.agda`
8. `DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`
9. `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`
10. `DASHI/Physics/Closure/ContractionSignatureToSpinDiracBridgeTheorem.agda`
11. `DASHI/Physics/Closure/CliffordToEvenWaveLiftBridgeTheorem.agda`
12. `DASHI/Physics/Closure/PhysicsClosureFull.agda`

## Module Labels

Use one of these labels for every closure-relevant module:

- `canonical`: part of the chain above, or required direct dependency of that
  chain.
- `alternative`: mathematically valid alternate derivation, not required for
  canonical closure claims.
- `validation`: independent cross-check route used to test canonical results.
- `experimental`: alternate proofs, prototypes, or candidate routes not yet on
  the canonical claim path.

## Current Labeling Rules

- Repo-facing closure claims (`README`, closure summaries, validation summaries)
  must reference `canonical` modules first.
- `alternative`, `validation`, and `experimental` modules may be referenced for
  context, but
  must not be presented as the primary proof path.
- If a module duplicates an existing canonical step, keep one canonical owner
  and label the rest `alternative`, `validation`, or `experimental`.

## Current Label Registry (First Pass)

### Canonical

- `DASHI/Geometry/ProjectionDefect.agda`
- `DASHI/Geometry/ProjectionDefectSplitForcesParallelogram.agda`
- `DASHI/Geometry/ProjectionDefectToParallelogram.agda`
- `DASHI/Geometry/QuadraticForm.agda`
- `DASHI/Physics/Closure/ContractionForcesQuadraticStrong.agda`
- `DASHI/Physics/Closure/ContractionForcesQuadraticTheorem.agda`
- `DASHI/Geometry/CausalForcesLorentz31.agda`
- `DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`
- `DASHI/Physics/Closure/ContractionSignatureToSpinDiracBridgeTheorem.agda`
- `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`
- `DASHI/Physics/Closure/CliffordToEvenWaveLiftBridgeTheorem.agda`
- `DASHI/Physics/Closure/PhysicsClosureFull.agda`

### Alternative

- `DASHI/Geometry/QuadraticFromNorm.agda`
- `DASHI/Geometry/QuadraticFromProjection.agda`
- `DASHI/Geometry/QuadraticFromParallelogram.agda`
- `DASHI/Geometry/QuadraticFormEmergence.agda`

### Validation

- `DASHI/Geometry/QuadraticEmergence.agda`
- `DASHI/Geometry/SignatureUniqueness31.agda`
- `DASHI/Physics/ContractionQuadraticBridge.agda`
- `DASHI/Physics/SignatureUniquenessOrbitLock.agda`

### Experimental

- `DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda`
- `DASHI/Physics/Closure/EmpiricalClosureWithSignatureLock.agda`
- `DASHI/Physics/Closure/PhysicsClosureInstanceAssumed.agda`

## Repo-Facing Citation Order

When updating repo-facing claim docs, cite in this order:

1. Canonical module(s) from the chain above.
2. Alternative or validation modules (if needed for local lemma context).
3. Experimental modules (only as alternatives/prototypes, never as primary
   evidence for closure claims).

## Change Control

Before adding a new closure theorem module:

1. State where it fits in the canonical chain.
2. If it does not fit, mark it `experimental` in docs/TODO.
3. Update `plan.md` and `TODO.md` with migration or de-duplication intent.

Before promoting a module from `experimental` to `canonical`:

1. Record why it replaces or extends a canonical step.
2. Update this file and repo-facing summaries in the same change.
3. Keep old path as compatibility/alternative/validation only until
   references are rewired.
