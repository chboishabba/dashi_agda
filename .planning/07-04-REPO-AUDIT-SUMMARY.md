# Repo Audit Summary (07-04)

## Accomplishments
- Created a table-driven module classification artifact to make the physics-critical path vs infrastructure explicit.
- Explicitly labeled `Verification/*` modules as non-core (tooling/experiment/presentational).
- Explicitly labeled closure seam modules (`DASHI/Physics/ClosureGlue.agda`, `DASHI/Physics/Signature31.agda`) as core.

## Notable Boundary Decisions
- "core": modules that appear to define or prove primary physics/closure/unification objects (the proof spine), or are explicit seams (`Signature31`, `ClosureGlue`).
- "plumbing": packaging/wiring/instance/default layers that exist to make the core reusable or configurable.
- "experiment": computed/specialized/external-integration modules that support exploration or cross-checks but are not required as the conceptual spine.
- "tooling": workflow harnesses, pipelines, profiling, scripts.
- "presentational": reader-facing summaries, reports, docs/README.

## Suggested Safe Refactor Candidates (Deferred; No Actions Taken)
- Split `Verification/*` into a separate package/subtree once classification is validated (keeps core compilation surface smaller).
- Consider grouping computed/generated orbit-profile modules under an explicit `Experiment` or `Generated` namespace.
- Keep closure seam modules stable and treat their public interfaces as refactor boundaries.

Deviations/issues: none.
