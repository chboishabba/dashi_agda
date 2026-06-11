# Proof-First Docs Reorg

Date: `2026-06-10`
Declared surface level: `execution-log`

This note records the first executed proof-first reorganization pass.

## Rule Applied

Visible `Docs/` surfaces should be:

- live paper manuscripts
- compact support directly consumed by those manuscripts
- compact reference and roadmap routers

Everything else should move behind `support/`, `roadmaps/`, `diagrams/`, or
`archive/`.

## Structural Changes

Created:

- `Docs/support/live/`
- `Docs/support/reference/`
- `Docs/roadmaps/`
- `Docs/diagrams/`
- `Docs/archive/authority/`
- `Docs/archive/domain-notes/`
- `Docs/archive/generated/`
- `Docs/archive/validation/`
- `Docs/archive/worker-packets/`

Moved paper support out of `Docs/papers/live/`:

- `SupportCompendium.md`
- `PaperCommonCitationLedger.md`
- `PaperCommonNotationGlossary.md`

Moved current non-paper support into `Docs/support/reference/`:

- `AgdaValidationTargets.md`
- `RepoGuide.md`
- `PhysicsGuide.md`
- `CurrentGateStatus.md`
- `ClosurePipeline.md`
- `ClosureContractStatus.md`
- `CanonicalProofSpine.md`
- `ContinuumLimit.md`
- `ConservedQuantities.md`
- `RealizationIndependence.md`
- `OperatorInvariantEquivalence.md`
- `ClaimComparisonEngine.md`
- `FinalAnalyticWalls.md`
- `NSAnalyticState.md`
- `YMAnalyticState.md`
- `UnifiedMathLanguageSpine.md`
- `UnifiedRoutesLanePlan.md`
- `MinimalCrediblePhysicsClosure.md`

Moved current planning surfaces into `Docs/roadmaps/`:

- `ClayNSProofRoadmap.md`
- `ClayYMProofRoadmap.md`
- `CorePhysicsTheoremRoadmap.md`
- `CompleteVerifiedPhysicsUnificationRoadmap.md`
- `SimulatorRoadmap.md`

Moved diagram assets into `Docs/diagrams/`.

Moved obvious historical/governance/domain material into `Docs/archive/`.

Archived obvious generated and validation debris from repo root into:

- `Docs/archive/generated/2026-06/`
- `Docs/archive/generated/2026-06/da51/`
- `Docs/archive/validation/2026-06/`

## Result

After this pass, `Docs/` root is intentionally minimal:

- `LiveSurfaceIndex.md`
- `ProofFirstRepoPolicy.md`
- `RepoStructureCleanupRoadmap.md`

This is the intended proof-first default reading layer.

## Deferred Work

- root-level markdown cleanup (`status.md`, `TODO.md`, `CHANGELOG.md`,
  `devlog.md`, `plan.md`, `spec.md`, `README.agda.md`)
- root-level standalone Agda sandbox/module cleanup
- `DASHI/Physics/Closure` support/archive lane moves after import-map staging
- historical path rewrites outside the high-signal routers
