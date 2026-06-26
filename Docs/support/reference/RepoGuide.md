# Repo Guide

Declared surface level: `packaging`.

This guide is for a new serious reader who needs the repo's structure, claim
boundaries, and practical entrypoints without reading every status surface.

## What This Repository Is

This repo is an Agda-first formalization workspace centered on DASHI geometry,
closure, and theorem-packaging layers, with supporting analysis, ontology, and
script surfaces. It contains both authoritative theorem modules and many
supporting documents that record current status, planning, experiments, or
empirical packaging.

For the repo-level simulator orientation, read `Docs/roadmaps/SimulatorRoadmap.md`.
It is the entrypoint for interpreting DASHI as a receipt-gated simulator
scaffold: objects inherit parent lane structure, speak the unified carrier
grammar, and only become quantitative through explicit receipts and
fail-closed promotion guards.
The first executable simulator slice is the bounded stellar-composition proxy
diagnostic in `scripts/run_stellar_composition_proxy_diagnostic.py`, guarded by
`DASHI.Unified.StellarCompositionProxyReceipt`; it does not promote stellar
evolution or solar-instability claims.
The repo-wide route joining plan is `Docs/support/reference/UnifiedRoutesLanePlan.md`; it extends
the same carrier -> observable -> receipt -> guard pattern across physics,
empirical, biology, runtime, arithmetic, Gate 3, NS, and YM lanes.

Use claim-level language carefully:

- `canonical` means authoritative for current repo claims.
- `strong` means a strengthened theorem surface with explicit seam witnesses.
- `validation` means cross-check or audit surface, not the canonical proof path.
- `experimental` or `theorem-thin` means packaging, scaffold, or bounded
  consumer surface, not a full derivation claim.

## Top-Level Structure

- `DASHI/`: main Agda codebase. This is the primary source of formal claims.
- `Kernel/` and `Verification/`: smaller foundational and proof-support
  surfaces that are suitable for routine validation.
- `Ontology/`: domain-specific formal lanes, especially Hecke and DNA.
- `Docs/`: canonical prose maps, bridge notes, validation policy, and diagrams.
- `scripts/`: validation helpers, routing tools, diagram rendering, and data
  preparation utilities.
- `artifacts/` and `data/`: generated or materialized support surfaces. These
  are usually evidence or inputs, not the theorem source of truth.
- `README.md`: repo-facing entry surface and current high-level status summary.
- `architecture.md`: canonical architecture and diagram entrypoint map.
- `Docs/support/reference/RepoIndexPlan.md`: repo-local symbol index plan and
  LSP-shaped discovery layer.

## Canonical Vs Status-Only Surfaces

Read these as authoritative or near-authoritative:

- `README.md` for current repo-facing orientation and diagram pointers.
- `Docs/roadmaps/SimulatorRoadmap.md` for the simulator scaffold, first quantitative
  slice, and cross-scale matter prediction boundary.
- `Docs/support/reference/UnifiedRoutesLanePlan.md` for the route/lane unification plan.
- `architecture.md` for the canonical theorem route and diagram entrypoints.
- `Docs/support/reference/CanonicalProofSpine.md` for the single proof spine to cite in docs and
  imports.
- `Docs/support/reference/AgdaValidationTargets.md` for what to compile in normal work loops.
- specific owner modules in `DASHI/` for the actual formal claim surface.

Read these as status, planning, or execution control surfaces rather than
authoritative theorem definitions:

- `status.md` and `status.json`
- `spec.md`
- `plan.md`
- `TODO.md`
- `COMPACTIFIED_CONTEXT.md`
- most thread-derived or packaging notes in `Docs/` unless they explicitly map
  back to canonical modules

Rule of thumb: if a prose document and an Agda owner module disagree, the owner
module wins. If two prose surfaces disagree, prefer `architecture.md`, then
`README.md`, then focused docs such as `Docs/support/reference/CanonicalProofSpine.md`.

## Theorem Spine Entrypoints

The repo's authoritative closure route is the canonical spine recorded in
`architecture.md` and restated in `spec.md`:

1. `DASHI.Geometry.ProjectionDefect`
2. `DASHI.Geometry.ProjectionDefectSplitForcesParallelogram`
3. `DASHI.Geometry.ProjectionDefectToParallelogram`
4. `DASHI.Geometry.QuadraticForm`
5. `DASHI.Physics.Closure.ContractionForcesQuadraticStrong`
6. `DASHI.Geometry.CausalForcesLorentz31`
7. `DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem`
8. `DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem`
9. `DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem`

For a reader, the practical theorem-spine entry docs are:

- `architecture.md`
- `Docs/support/reference/CanonicalProofSpine.md`
- `Docs/support/reference/ClosureContractStatus.md`

Important boundary:

- this spine is the required route for current closure claims
- alternate derivation routes may exist in the tree, but they should be read as
  `alternative`, `validation`, or `experimental` unless explicitly promoted

## Build And Validation Surfaces

For routine work, do not start with the largest aggregates.

Preferred focused validation policy:

- use the targets listed in `Docs/support/reference/AgdaValidationTargets.md`
- compile one or two canonical bridge modules directly during local edits
- use `DASHI/Physics/Closure/PhysicsClosureSummary.agda` for a broader but still
  manageable canonical summary

Known heavy or bounded-only surfaces:

- `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`
- `DASHI/Everything.agda`
- `DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`
- `DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda`
- `DASHI/Physics/DashiDynamicsShiftInstance.agda`
- `DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda`
- `DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda`
- `DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda`
- `DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda`
- `DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda`
- `DASHI/Physics/Closure/CanonicalStageC.agda` as a checkpoint, not a default
  inner-loop target

Policy:

- `L0` and `L1` decide branch truth, roadmap truth, and theorem promotion.
- `L2` does not decide branch truth. It is reserved for closure certification.
- If a theorem-owner or blocker surface is classified through `L0`/`L1`, do not
  reroute that decision back through `Everything.agda` or
  `PhysicsClosureValidationSummary.agda`.

Reason:

- `Everything.agda` and `PhysicsClosureValidationSummary.agda` are still the
  obvious top-level aggregates.
- The listed closure recovery modules form the current hot path that repeatedly
  pulls the expensive shift-observable, canonical-gauge, and known-limits
  theorem stack into local validation runs.
- `CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda` appears
  structurally live, but it should remain blacklisted from routine checks until
  that dependency path is made cheaper.

Offline closure certification:

- treat `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda` as the
  single aggregate closure target
- run it as a batch job, not as part of the interactive loop
- use `scripts/run_closure_full_check.sh` for the aggregate pass
- classify the result only as `clean`, `error`, or `too_large`

Useful script entrypoints:

- `scripts/run_agda_easy_to_hard.py`
- `scripts/route_agda_by_layer.py`
- `scripts/run_closure_hygiene.py`
- `scripts/run_closure_full_check.sh`
- `scripts/render_docs_diagrams.sh`

## Docs, Diagrams, And Modules

The docs are best read as maps to code, not replacements for code.

Current canonical diagram surfaces:

- `Docs/diagrams/ObservableSignatureGaugeEntryRound.puml`
- `Docs/diagrams/ObservableSignatureGaugeEntryRound.svg`
- `Docs/diagrams/TRAINING_DYNAMICS.puml`
- `Docs/diagrams/TRAINING_DYNAMICS.svg`

Diagram policy:

- `.puml` is the diffable source of truth
- `.svg` is the rendered preview
- regenerate previews with `./scripts/render_docs_diagrams.sh`
- use `architecture.md` as the canonical textual entrypoint for diagrams

Clay sprint artifact policy:

- `Docs/diagrams/Images/clay-analytic-sprint/` contains generated diagnostics
  and replay evidence, not hand-maintained source
- keep compact summaries/manifests/checks in git when they are used as stable
  receipts
- do not commit oversized row-level dumps such as
  `ns_packet_transition_table.csv`; regenerate them from the NS diagnostic
  harness when needed
- Sprint 48 replenishment replay can be rebuilt from the tracked Sprint 47
  `ns_packet_transition_summary.csv` inputs via `scripts/ns_diagnostic_harness.py`

Module-to-doc relation:

- `architecture.md` and `Docs/support/reference/CanonicalProofSpine.md` map the main closure path
- `Docs/support/reference/AgdaValidationTargets.md` maps code modules to validation practice
- `Docs/support/reference/RepoIndexPlan.md` maps the discovery/index layer to
  the Agda-grounded project graph
- focused docs in `Docs/` usually explain one lane, gap, or consumer layer and
  should be read alongside the cited Agda modules

## Recommended Reading Order For Engineers

1. `README.md`
2. `Docs/roadmaps/SimulatorRoadmap.md`
3. `Docs/support/reference/UnifiedMathLanguageSpine.md`
4. `architecture.md`
5. `Docs/support/reference/CanonicalProofSpine.md`
6. `Docs/support/reference/AgdaValidationTargets.md`
7. the canonical spine modules themselves, in order
8. `Docs/support/reference/ClosureContractStatus.md` for the current seam boundary
9. only then read lane-specific docs in `Docs/` that match the subsystem you
   are touching

If you are editing code rather than auditing it:

1. identify whether your target is `canonical`, `validation`, or
   `experimental`
2. validate the narrowest owner module first
3. avoid treating `Everything.agda` or large status docs as the primary source
   of truth

## Formal Owner Modules

These are the modules a reader should treat as owner surfaces for the current
closure path:

- `DASHI/Geometry/ProjectionDefect.agda`
- `DASHI/Geometry/ProjectionDefectSplitForcesParallelogram.agda`
- `DASHI/Geometry/ProjectionDefectToParallelogram.agda`
- `DASHI/Geometry/QuadraticForm.agda`
- `DASHI/Physics/Closure/ContractionForcesQuadraticStrong.agda`
- `DASHI/Geometry/CausalForcesLorentz31.agda`
- `DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`
- `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`
- `DASHI/Physics/Closure/CliffordToEvenWaveLiftBridgeTheorem.agda`

## Consumer Modules

These are important consumers, bundles, summaries, or downstream packaging
surfaces, but they should not be confused with the entire proof spine:

- `DASHI/Physics/Closure/CanonicalContractionToCliffordBridgeTheorem.agda`
- `DASHI/Physics/Closure/PhysicsClosureFullInstance.agda`
- `DASHI/Physics/Closure/MinimalCrediblePhysicsClosureShiftInstance.agda`
- `DASHI/Physics/Closure/KnownLimitsGRBridgeTheorem.agda`
- `DASHI/Physics/Closure/KnownLimitsQFTBridgeTheorem.agda`
- `DASHI/Physics/Closure/PhysicsClosureSummary.agda`
- `DASHI/Physics/Closure/Canonical/LocalProgramBundle.agda`
- `DASHI/Physics/Closure/Canonical/Ladder.agda`

## Not This / Out Of Scope

- Do not read `status.md`, `TODO.md`, or thread-derived notes as if they were
  the theorem source of truth.
- Do not treat `DASHI/Everything.agda` as the normal starting point for local
  work; it is authoritative but too aggregate for routine use.
- Do not interpret theorem-thin, empirical, or packaging lanes as closure proofs
  unless the owner module explicitly promotes that claim.
- Do not infer that every subdirectory under `DASHI/`, `Ontology/`, or `Monster/`
  participates in the canonical closure path.
