# Canonical ITIR × SLR fleet adapter — source-audited cut, 2026-10-26

## Source owners and historical status

Inspected directly (read-only):
- `chboishabba/ITIR-suite/scripts/autonomous_fleet_daemon.py`: historical round-robin carousel, **not** a safe default integration target.
- `chboishabba/ITIR-suite/docs/planning/frontier_evidence_engine_v1.md`: metadata-only canonical frontier, bounded evaluation, ledger ownership, no dispatch.
- `chboishabba/ITIR-suite/docs/planning/frontier_typed_receipts_v1.md`: exact source-thread mapping, verified typed operation/repo/formal refs, holds on unresolved evidence.
- `chboishabba/ITIR-suite/docs/planning/governed_revival_handoff_v1.md`: explicit warning about historical daemon's title prompts and unsafe DOM fallback; governed read-only handoff.
- `chboishabba/slr/crates/sl-proof-search-scheduler/src/lib.rs`: offline-first proof-gap/candidate/Pareto selector with permission-gated live moves.
- `chboishabba/slr/crates/sl-proof-search-loop/src/receipt.rs`: canonical iteration receipt v0.1 and frontier iteration v0.2.

This crosswalk is new analysis by Johl Brown with OpenAI ChatGPT assistance. The original module authors retain their source authorship. No external runtime, corpus, fleet, formal compiler, or database was executed.

## Canonical division of responsibility

**DASHI/Agda** owns exact observer collision, conditional consumer factorization and future-language obligations. Its source-written `RevisableObserverConsumerFactorizationExact` is a mathematical candidate pending Agda typecheck.

**SLR** owns the offline-first candidate scheduler and its `ProofGap`, `CandidateMove`, `ExecutionCostVector`, `ProofValueVector`, `ExecutionPermission`, `CanonicalIterationReceipt`. Existing `authority_boundary = experimental_candidate_only` is preserved. A live move needs separately governed adapter authority.

**ITIR MCP** owns canonical archive mapping, bounded source acquisition, verified typed frontier references, candidate ledger and governed revival. The frontier engine must not read bulk transcript bodies, infer PRs from titles/timestamps, or dispatch on its own.

**AO** may own execution lifecycle and worker receipts after a separately authorised dispatch; a worker exit code cannot create theorem, evidence or institutional authority.

## Concrete residual-to-task adapter mapping

- Consumer-relative collision witness -> SLR `ProofGap.consumer_ref` and `residual_ref`; missing proposition = requested distinguishing coordinate; required producer = theorem search or experimental discriminator.
- Exact Agda module/source head -> typed repository reference, initially *held* until source identity and head independently resolved; a path/hash is not kernel verification.
- Source-root literature discovery -> `CandidateMove.source_ref` with provenance, original/secondary relationship and bounded search scope.
- Proposed route -> `CandidateMove.strategy`, `provider_operation_ref`, `cost`, `value`, `admissible`, `calibration_ref`.
- SLR selection -> `CanonicalIterationReceipt` including `frontier_ref`, `selected_move_ref`, `input_digest_ref`, `output_digest_ref`, `frontier_delta_ref`, `next_move_ref`, and optional artifact/PNF references.
- ITIR admission -> `validate_typed_references` plus canonical thread mapping; unresolved/ambiguous references are explicit holds; ledger owns transitions.
- Changed evidence -> DASHI selective invalidation dependency frontier; unaffected consumers remain unchanged subject to explicit preservation assumptions.

## Required regression / acceptance matrix

1. Equal observation, different consumer answer: no decoder; emits candidate residual only.
2. No suitable source within bounded search: `not_found_in_scope`, not `historically_original`.
3. Successful worker exit without formal verification: candidate only.
4. SHA/path without independent formal verifier: hold.
5. Duplicate reprint sharing original source root: not two independent corroborations.
6. Changed relevant source revision: invalidate only dependency-reachable consumers.
7. Offline candidate move: scheduler may select; no implicit live dispatch.
8. Governed live move: explicit external permission required.
9. Commit-unknown operation: no automatic resend.
10. Collaborative Alice/ESD scope: conceptual reuse is not team adoption.

## Execution order

**G0 (done):** locate canonical owners and correct the carousel misconception.
**G1:** focused Agda typecheck and positive/negative consumer fixtures.
**G2:** implement a *read-only* adapter on the actual SLR/ITIR schema, with fixture tests and exact source refs; do not write a new scheduler.
**G3:** run offline candidate selection and produce v0.2 frontier iteration receipts with deterministic input/output digests.
**G4:** ITIR typed-reference validation, ledger admission and selective invalidation tests.
**G5:** only then propose separately authorised execution integration.

## Hard holds

The historical `autonomous_fleet_daemon.py` must not be used as a production route merely because it exists. The canonical corpus `~/chat_archive.sqlite` is not interchangeable with transport cache. No raw bodies in frontier discovery; no title/age as evidence; no automatic mutation/DOM/resend; no unverified kernel claims; no ESD team integration without approval.

**Current status:** source audit and crosswalk only. No SLR/ITIR code changes, no kernel receipt, no live fleet operation.
