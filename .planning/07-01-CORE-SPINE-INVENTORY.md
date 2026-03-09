# 07-01 Core Spine Inventory

Goal: Identify the physics-critical spine (core seam) vs plumbing vs experiments/tooling.

## Confirmed Core Seam Modules

- `DASHI/Physics/ClosureGlue.agda`
  - Category: core
  - Why: Defines `record ClosureAxioms : Set₁` (the physics interface seam), plus derived facts and defaults.

- `DASHI/Physics/RealOperators.agda`
  - Category: core (operator surface)
  - Why: Defines the current real-operator triad `Pᵣ`, `Cᵣ`, `Rᵣ` and nonexpansive proofs.
  - Note: `Cᵣ` and `Rᵣ` are currently identity; `Pᵣ` is a concrete projection-like operation.

- `DASHI/Physics/RealOperatorStack.agda`
  - Category: plumbing (stack wiring)
  - Why: Wires `C/P/R` aliases and proofs (nonexpansive + fiber contractivity glue).

- `DASHI/Physics/Signature31.agda`
  - Category: seam (signature surface)
  - Why: Exposes `sig31` and a `SignatureTheorem` record, but the current theorem implementation is trivial (returns `sig31` with `refl`).

- `DASHI/Physics/Closure/PhysicsClosureSummary.agda`
  - Category: presentational index
  - Why: Repo-facing entrypoint; re-exports the canonical Stage C ladder and documents what is theorem-critical vs prototype-only.

- `DASHI/Everything.agda`
  - Category: presentational/entrypoint
  - Why: Aggregated compile entrypoint for the whole repo.

## Likely Core Signature Forcing / Stage B Surface (Not Exhaustive)

These appear to be on the signature-forcing path (need tighter diagramging next):

- `DASHI/Geometry/Signature31FromConeArrowIsotropy.agda` (core forcing lemma surface)
- `DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda` (core forcing lemma surface)
- `DASHI/Physics/Signature31FromShiftOrbitProfile.agda` (core realization-specific bridge)

## Explicit Experiments/Tooling

- `Verification/Pipeline.agda` (experiment/tooling)
- `Verification/CostProfile.agda` (tooling)
- `Verification/LMFDB.agda` (experiment)
- `Verification/ZK.agda` (experiment)

Rationale: These modules support validation/profiling/certification but are not part of the proof spine; they should not be imported by bridge/core modules.

## Notes / Gaps (What This Inventory Surfaces)

- The repo’s correct abstraction layer already exists: `ClosureAxioms` (`DASHI/Physics/ClosureGlue.agda`).
- The “missing substance” critique is concretely visible: `Cᵣ` and `Rᵣ` are identity today (`DASHI/Physics/RealOperators.agda`).
- The signature surface exists but at least one `Signature31` theorem is currently trivial (`DASHI/Physics/Signature31.agda`).

Next: produce a canonical dependency diagram that separates:
- Closure interface (`ClosureAxioms`)
- Operator layer (`Cᵣ/Pᵣ/Rᵣ` + proofs)
- Signature forcing chain (Stage B)
- Canonical Stage C entrypoints (as re-exported by `PhysicsClosureSummary`).
