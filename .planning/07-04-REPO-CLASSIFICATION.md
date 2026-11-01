# Repo Classification (07-04)

Goal: identify the physics-proof-critical spine vs repo infrastructure, without moving files.

| module path | category | why it exists | depends-on (optional) |
|---|---|---|---|
| `DASHI/Physics/Core.agda` | core | Primary physics development entry module for core definitions/lemmas used broadly. | `DASHI/Physics/*` |
| `DASHI/Physics/Signature31.agda` | core | Canonical signature target (31) used as a key seam in closure/unification arguments. | `DASHI/Physics/Signature*` |
| `DASHI/Physics/ClosureGlue.agda` | core | Closure seam/glue layer that wires closure kit/status into the physics development. | `DASHI/Physics/Closure/*` |
| `DASHI/Physics/Closure/PhysicsClosureSummary.agda` | presentational | Canonical summary/overview entrypoint for closure results (reader-facing consolidation). | `DASHI/Physics/Closure*`, `DASHI/Physics/ClosureGlue.agda` |
| `DASHI/Physics/ClosureBuilder.agda` | plumbing | Builds closure artifacts/records used by downstream closure proofs. | `DASHI/Physics/Closure*` |
| `DASHI/Physics/DefaultClosure.agda` | plumbing | Provides default instances/configurations for closure computations/proofs. | `DASHI/Physics/Closure*` |
| `DASHI/Physics/ClosureStatusFromGlue.agda` | plumbing | Extracts/derives closure status/results from glue wiring for reuse. | `DASHI/Physics/ClosureGlue.agda` |
| `DASHI/Physics/UnificationClosure.agda` | core | Unification-focused closure theorem/proof layer tying major components together. | `DASHI/Physics/Closure*` |
| `DASHI/Physics/UnifiedClosure.agda` | core | Consolidated closure development intended as a stable endpoint for proofs. | `DASHI/Physics/UnificationClosure.agda` |
| `DASHI/Physics/RealOperators.agda` | core | Core operator layer used by physics constructions (operator semantics/lemmas). | `DASHI/Physics/RealOperator*` |
| `DASHI/Physics/RealOperatorStack.agda` | plumbing | Stack/packaging of real-operator components for reuse across proofs. | `DASHI/Physics/RealOperators.agda` |
| `DASHI/Physics/SeverityMapping.agda` | plumbing | Infrastructure for severity/guard mapping used to control proof obligations/variants. | `DASHI/Physics/SeverityGuard*` |
| `DASHI/Physics/OrbitProfileData.agda` | plumbing | Defines orbit-profile data structures used across orbit/fingerprint computation modules. | `DASHI/Physics/OrbitProfile*` |
| `DASHI/Physics/OrbitProfileComputed.agda` | experiment | Generated/computed orbit profile material; useful but not the conceptual spine. | `DASHI/Physics/OrbitProfileData.agda` |
| `DASHI/Physics/MaassRestorationShift.agda` | experiment | Specialized restoration/shift experiments; exploratory and likely refactorable. | (not confirmed) |
| `Verification/Pipeline.agda` | tooling | Orchestrates verification runs/pipelines; supports workflow, not proof spine. | `Verification/*` |
| `Verification/CostProfile.agda` | tooling | Cost/performance profiling harness for proof/module evaluation. | `Verification/Prelude.agda` |
| `Verification/LMFDB.agda` | experiment | External-data (LMFDB) integration experiments for cross-checking/lookup. | `Verification/Prelude.agda` |
| `Verification/ZK.agda` | experiment | Zero-knowledge / proof-carrying experiments; not required for core compilation. | `Verification/Prelude.agda` |
| `Verification/BinaryPatching.agda` | tooling | Auxiliary tooling for patching/inspection; workflow support. | (not confirmed) |
| `Verification/ExecutionReview.agda` | presentational | Human-readable reporting/review of verification execution runs. | `Verification/Pipeline.agda` |
| `scripts/` | tooling | Shell/scripts for building, running, or exporting artifacts. | (not confirmed) |
| `docs/` | presentational | Documentation and narrative materials for readers. | (not confirmed) |
| `README.md` | presentational | Repo entrypoint for humans; high-level description and pointers. | (not confirmed) |
