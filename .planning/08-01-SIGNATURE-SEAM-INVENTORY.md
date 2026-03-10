# 08-01 Signature Seam Inventory

Goal: identify all repo entrypoints that provide a `sig31` / Signature31 claim, and classify which are trivial vs theorem-critical, and which path is canonical for the Stage C closure ladder.

## Entry Points Providing `sig31` / Signature31 Claims

- `DASHI/Physics/Signature31.agda`
  - Provides: `sig31 : Signature` (local record) and
    `involution+isotropy+finiteSpeed⇒signature31` returning a `SignatureTheorem` with `signature = λ _ → sig31` (definitionally trivial witness).
  - Category: trivial
  - Notes: this is a prototype-style filler: it manufactures a `SignatureTheorem` without using its inputs.

- `DASHI/Physics/Signature31FromShiftOrbitProfile.agda`
  - Provides: `signature31 : DASHI.Geometry.ConeTimeIsotropy.Signature` plus `signature31-theorem : Signature31Theorem`.
  - Category: realization-specific theorem
  - Notes: explicitly intended as the “headline theorem module for the current repo state”; sourced from `DASHI.Physics.Signature31IntrinsicShiftInstance`.

- `DASHI/Geometry/Signature31FromConeArrowIsotropy.agda`
  - Provides: Signature31 theorem/claim derived from cone + arrow + isotropy bridge.
  - Category: realization-specific theorem (bridge)
  - Notes: geometry-side bridge surface; likely consumed indirectly by shift realization instances.

- `DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda`
  - Provides: Signature31 theorem/claim derived from intrinsic shell-forcing.
  - Category: realization-specific theorem (bridge)

- `DASHI/Geometry/Signature/Elimination.agda`
  - Provides: eliminators/transport for signature claims (infrastructure; may re-express signature equalities).
  - Category: canonical export (supporting infrastructure)

- `DASHI/Geometry/Signature31Lock.agda`
  - Provides: lock/uniqueness style constraint tying a signature claim to a discriminant path.
  - Category: assumption-based (lock) / supporting infrastructure
  - Notes: depends on details; intended to prevent signature ambiguity.

## Canonical Stage C Ladder Surface (Dependency Index)

Starting index: `DASHI/Physics/Closure/PhysicsClosureSummary.agda`.

Observed signature seam-related imports/exports in the canonical summary:

- Canonical Stage C ladder is exported primarily via:
  - `open import DASHI.Physics.Closure.CanonicalStageC as CSC public`
  - plus associated canonical status / witness / theorem bundles.

- The summary explicitly re-exports the realization-specific signature path:
  - `open import DASHI.Physics.Signature31FromShiftOrbitProfile as S31OP public`

- The summary does NOT currently import or re-export `DASHI/Physics/Signature31.agda`.
  - Therefore, the closure summary’s canonical route to a `sig31` value is already through the shift-orbit-profile theorem module, not through the trivial witness module.

## Classification Summary

- Trivial/prototype-only:
  - `DASHI/Physics/Signature31.agda`

- Theorem-critical (currently realization-specific):
  - `DASHI/Physics/Signature31FromShiftOrbitProfile.agda`
  - `DASHI/Geometry/Signature31FromConeArrowIsotropy.agda`
  - `DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda`

- Canonical export / infrastructure:
  - `DASHI/Geometry/Signature/Elimination.agda`
  - `DASHI/Geometry/Signature31Lock.agda`

## Canonical Decision (as of current tree)

- Canonical closure summary points at the theorem-critical signature seam via
  `DASHI/Physics/Signature31FromShiftOrbitProfile.agda`.
- `DASHI/Physics/Signature31.agda` is a prototype/trivial witness module and must remain isolated from canonical imports/exports.
