# Semantic thread rejuvenation — golden Agda boundary

Owner: `DASHI/Interop/SemanticThreadRejuvenationExact.agda`.
Runtime: `chboishabba/reverse-engineered-chatgpt/re_gpt/revive.py` and `chboishabba/ITIR-suite/itir-mcp`.

## Five stages

1. `Thread`: source conversation identity.
2. `PNF source`: source-indexed candidate factors.
3. `World source factors`: world registration receipt.
4. `WorldRelative source factors registered`: contextual capsule.
5. `Rejuvenated source factors registered relativeState`: child and lineage receipt.

The dependent indices prevent accidentally composing stages from different source values in the typed model. The runtime must implement and test the corresponding checks. This module does not establish runtime correctness.

## Authority and evidence

`Database` has one constructor: `postgresql`. This models the mandated authoritative store, not proof that deployed services have stopped using SQLite.

`lineagePreserved` and `enrichmentCannotPromoteProof` project evidence supplied to the final stage. They do not independently verify the truth of an external lineage record or a theorem.

No Agda postulates, holes, or TERMINATING pragmas are used. Kernel verification is pending.

## Reuse and integration

- `DASHI.Interop.HierarchicalSpectralParetoExact` (PR #1416): quotient coarsening, eligible topics, alpha ordering, worker bounds.
- `DASHI.Interop.SublinearTopicConductorCostExact` (PR #1417): worker width, cost formula, no proof-authority promotion.
- Keep these imported from their owners after the relevant PRs land; do not copy the algorithms.
- Do not edit ESD modules.

## Execution roadmap

| Phase | Deliverable | Acceptance |
| --- | --- | --- |
| R0 | Inventory PostgreSQL tables, archive and runtime call sites | Documented schemas and dependencies |
| R1 | Idempotent PostgreSQL migration and backfill | Counts, hashes, referential integrity, rollback |
| R2 | Five-stage semantic pipeline and typed provenance | Reproducible factor and capsule receipts |
| R3 | Async curl_cffi dispatch with durable outbox | Crash/retry and duplicate-send tests |
| R4 | Formal parity and Lean bridge | Agda kernel, Lean kernel, Python tests |
| R5 | AO tranche activation | PostgreSQL-only runtime audit and supervised canary |
| R6 | Retire SQLite/.slrw | Verified backups and deletion receipts |

## Unproved runtime obligations

- Exactly-once logical dispatch requires idempotency keys and reconciliation.
- Capsule soundness requires evidence references, not word matching.
- Proven theorem claims require independently verified kernel receipts.
- PostgreSQL world writes must be atomic with lineage/outbox state.
- Database deletion requires successful backfill, independent backup and recovery tests.
- Continuous Pareto metrics require an explicitly defined ordered carrier and comparison; the Agda owner does not assume hidden real-number arithmetic.

## Attribution

Inherited mathematical foundations remain credited to their original authors. Repository source, computational checks, and kernel-verified theorems are separate categories. Existing Ibrahim Monster 3B ownership is preserved. Shared fingerprints or analogies are not same-object representation proofs.
