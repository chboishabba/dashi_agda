# October 26 fleet delta: AO-OP-1 and source-bound proof-search crosswalk

## What changed since the previous fleet audit

Inspected current ITIR-suite main commits through `34df7d9e1` (2026-10-26) and merged PRs #25, #32, #33, #34, #35; inspected SLR current head `1db8aeee8` and `dashi_agda` recent PRs. Original source authorship belongs to the owning repositories; this synthesis is Johl Brown with OpenAI ChatGPT assistance.

**Correction to prior roadmap:** ITIR AO-OP-1 already implements a bounded read-only canonical evidence-to-handoff operator workflow. It composes the existing frontier ledger, typed reference validator, work packet, governed handoff and operation review. It is NOT necessary to implement another operator handoff workflow in DASHI. See `ITIR-suite/docs/planning/ao_operator_workflow_v1.md` and `itir-mcp/src/itir_mcp/operator_workflow.py`.

AO-OP-1 accepts explicit canonical thread IDs and bounded task atoms, limits candidate and output sizes, and reports next-review actions without dispatch or promotion. A verified PNF resolver exists as an internal trusted composition seam, but is **not** wired to production MCP; user-supplied receipt labels cannot grant verification. It permits actionable *review-only* candidates even when PNF/PG is unavailable, while retaining the formal authority hold.

## Remaining actual cross-repo cut

| Concern | Canonical owner | Status |
| --- | --- | --- |
| Consumer no-decoder theorem | DASHI `RevisableObserverConsumerFactorizationExact` | Source-written, not Agda-checked |
| Future-safe observer refinement | DASHI `ObserverFactorizedRefinementExact` | Existing |
| Candidate/Pareto selector | SLR `sl-proof-search-scheduler` | Existing offline-first |
| Proof frontier iteration receipt | SLR `sl-proof-search-loop/receipt.rs` | Existing v0.1/v0.2 |
| Canonical frontier and ledger | ITIR MCP `frontier_evidence` | Existing |
| Typed evidence holds | ITIR MCP `frontier_reference_validation` | Existing |
| Read-only operator handoff | ITIR MCP `operator_workflow` | **Already implemented** |
| Producer-owned verified PNF | ITIR MCP resolver seam | Not wired to production MCP |
| Independent formal verifier | SLR/Agda/Lean checker adapter | Not wired end-to-end |
| SLR iteration -> ITIR canonical handoff mapping | Cross-repo adapter | Not demonstrated end-to-end |
| Selective invalidation -> incremental candidate reopening | DASHI/SLR/ITIR | Formal primitives exist; end-to-end receipt join unverified |

## Max-cut change of priority

**P0** Kernel-check the DASHI consumer lemma and pin exact module SHA. This is the only new Agda proof surface in #1266.

**P1** Define a fixture-only SLR `CanonicalFrontierIterationReceiptV02` -> ITIR `itir.ao.operator_workflow` candidate mapping using *actual* schemas, not a replacement scheduler. Require exact `canonical_thread_id` mapping from canonical archive; a SLR `consumer_ref` or `source_ref` alone cannot establish it. Where no exact mapping exists, emit an explicit hold.

**P2** Add integration tests: deterministic digest, unique canonical thread, bounded task atom, no raw bodies, untrusted PNF hold, commit-unknown hold, candidate-only review, no mutation and no dispatch.

**P3** Wire independently trusted producer/verifier adapters, starting with repository head verification then focused Agda kernel check, and separately verified PNF. Never let GitHub SHA, CI status, a worker exit code or PNF label substitute for the specific proof receipt.

**P4** Replay changed source/proof receipts into selective invalidation; require dependency-bound reopening, historical attribution preservation and unaffected consumer stability.

**P5** Governed execution is a distinct, later authority transition. Do not revive `scripts/autonomous_fleet_daemon.py` round-robin/DOM fallback.

## Cross-pollination with latest Agda PRs

- #1255: prefix noninterference and source/arrival order, candidate test for historical identity.
- #1254: exotic topology ancestry collision, candidate non-decoder test.
- #1262: carrier action vs invariant observable, candidate preservation failure.
- #1263: experimental discriminator authority and calibration, candidate proof-vs-experiment split.
- #1264: ESD integration permission boundary, candidate institutional-authority test.
- #1250/#1098: action-first same-object character transport, requires object-level witness before analogy-based reuse.

## Acceptance gate

The next cross-repo milestone is *not* a new fleet controller. It is a reproducible offline fixture where an exact DASHI residual enters SLR's existing candidate selection, SLR emits its canonical v0.2 receipt, ITIR maps it to exactly one canonical source thread and returns an actionable **review-only** handoff with verified/held authority recorded. No dispatch and no theorem promotion. Kernel and semantic verifier integration remain independent milestones.

**Evidence status:** repository source audit; no runtime execution or checker receipt in this change.
