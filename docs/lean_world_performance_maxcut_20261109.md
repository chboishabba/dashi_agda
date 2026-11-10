# Lean World throughput and memory gate — independent performance tranche

This branch is separate from PR #1483. It does not touch the worker's dirty
Karp21 checkout or change PR #1483's index implementation.

## Reproduced baseline (2026-11-09)

Using a locally reproduced implementation of PR #1483's FibreIndex, a single
adversarially large fibre, four declarations per exact type, 20 returned
candidates and synthetic source metadata:

| Declarations | Throughput (declarations/s) | Peak traced memory | Median lookup |
|---:|---:|---:|---:|
| 1,000 | 37,908 | 0.69 MiB | 0.352 ms |
| 10,000 | 33,210 | 6.96 MiB | 5.863 ms |
| 30,000 | 35,262 | 21.88 MiB | 20.941 ms |
| 50,000 | 25,621 | 35.65 MiB | 52.833 ms |
| 100,000 | 20,294 | 71.42 MiB | 149.064 ms |

Timings are host/memory/GC dependent and **not** Lean parsing, PostgreSQL, or
whole-corpus measurements. A fresh run of the checked-out PR must confirm them.
The benchmark file `scripts/bench_lean_fibre_index.py` is designed to import
PR #1483's module after checkout.

## Critical code path

Current `FibreIndex.candidates` invokes `sorted(self._fibre[projection])` for
every query, so a fibre of size `m` performs O(m log m) ordering regardless of
output budget `k`. Hash grouping helps exact ingestion but does not resolve
this lookup cost.

Recommended persistent implementation: PostgreSQL B-tree ordered by
`(fibre_id, repository, revision, declaration)`, with keyset pagination and
LIMIT. For an indexed warm read this changes the *algorithmic target* to
O(log N + k), excluding storage access, cache misses and snapshot overhead.
Use fibre identifiers, not arbitrary user-supplied hash keys, for indexes.

## Existing formal boundary

A fibre projection is an admissible search restriction, not a theorem
equivalence. Preserve source occurrences and independent proof digests.
Candidate reduction cannot silently claim exhaustive semantic recall.
Check canonical_type bytes on SHA-256 hits, even when the digest matches.

## New PostgreSQL schema proposal

`scripts/sql/lean_world_fibre_search_v1.sql` provides a standalone
illustrative schema: fibres, canonical statement bytes, provenance occurrences,
digest lookup, B-tree keyset indexing, and statement-level batched count
maintenance. Its use is **not yet integrated or migration-tested** against the
existing production PostgreSQL owner.

Importer requirements:
- Source-pinned Lean exporter, foundation/profile identification and validated
  canonical term serialization.
- Concurrent statement identity admission must use a transaction-scoped
  per-(fibre,digest) lock, then compare canonical_type bytes before reusing
  statement_id; a SHA match alone is not sufficient.
- Reject conflicting repository/revision/declaration identities. Do not
  `ON CONFLICT DO NOTHING` on an incompatible repeated origin.
- Bulk insert/COPY source occurrences in bounded chunks; keep large canonical
  bytes in the statement table, not repeated in every occurrence.
- Ensure `fibre_id` on occurrence matches referenced statement (composite FK).
- Treat the stored count as exact for a consistent transaction/snapshot and
  first-page lookup; later-page exact omitted-count reporting needs extra rank
  metadata or a COUNT scan.
- Do not use an unversioned keyset cursor across concurrently changing world
  snapshots. Carry a generation or pin a transaction snapshot.
- Before production, test schema migration, count triggers, concurrency and
  explain plans against PostgreSQL. No database server was run in this tranche.

## Exact performance gates

| Gate | Acceptance evidence |
| --- | --- |
| PERF01 | Pin environment/versions; benchmark raw repo acquisition, Lean elaboration, type export, ingest, indexing, candidate query separately |
| PERF02 | Profile p50/p95/p99 fibre query latencies at 10k, 100k, 1m and 10m occurrences, for hot and cold cache |
| PERF03 | Measure peak RSS, DB size, WAL bytes, CPU and write amplification for real representative Lean records |
| PERF04 | Show keyset pagination with bounded per-page cost and correct snapshot semantics |
| PERF05 | Show digest collision controls, source provenance and type-byte equality preserved at scale |
| PERF06 | Benchmark bulk inserts with multiple workers, detect lock contention and validate fibre counts |
| PERF07 | Test complete exact matching within selected admitted fragment; report recall bounds for semantic retrieval |
| PERF08 | Run incremental update/delete/revision invalidation and measure affected closure size |
| PERF09 | Produce real 21,481-repository coverage metrics, with separately reported fetch, elaboration, parse failures and unprocessed queue |
| PERF10 | Run a real original-obligation → ranked donor → kernel-check path and measure each stage |

Performance targets should be set from measured hardware, dataset distributions
and intended concurrency. This tranche does not assert unrealistic end-to-end
runtime targets or confuse 21,481 repository identities with parsed declarations.


## Zero-checkout source acquisition (added 2026-11-10)

Two new source-only ingestion paths are available in this PR:

1. `scripts/lean_remote_source_inventory.py`: GitHub REST tree + pinned
   SHA-1 Git blobs. Per-blob SHA-1 identity is verified against content and
   SHA-256 is independently recorded. Handles authenticated private repos if
   `GITHUB_TOKEN` is provided. Refuses truncated recursive tree listings,
   oversized blobs, corrupt bytes, or non-immutable revision names. No files
   are downloaded to permanent checkout directories; JSONL can stream stdout.
   **API requests scale with number of Lean files**, not one per repository.
2. `scripts/lean_remote_archive_stream.py`: one pinned **public** codeload
   tar.gz stream per repository, processed using Python's tarfile stream mode.
   Never extracts to disk; emits source fingerprints and skipped-size markers.
   This avoids one metadata request per source file, at the cost of transferring
   archive data (including non-Lean files). Private/authenticated repositories
   are not supported by this public codeload mode.

All source records explicitly say `source-verified-not-elaborated`.
Content-addressed source identity is **not** Lean kernel acceptance. Archive
mode verifies each extracted .lean file as a Git SHA-1 blob, but archive
completeness/commit-to-tree correspondence still requires remote Git tree
validation or an independently trusted pinned archive provider.

Offline negative-control tests:
```sh
python3 -m unittest discover -s tests -p 'test_lean_remote_source_inventory.py' -v
python3 -m unittest discover -s tests -p 'test_lean_remote_archive_stream.py' -v
```
These tests are authored but **not executed from the GitHub connector**.
The worker's worktrees remain separate from these GitHub branch updates.

### Next mandatory architecture gate: real remote/ephemeral Lean elaboration

Lean kernel term export cannot be inferred from .lean file bytes, and it cannot
run inside GitHub's REST source API. For a real elaborated world, implement a
bounded Nix-managed worker:

- Use source inventory to identify candidate repos and pinned commits.
- Resolve exact `lean-toolchain`, `lakefile`, lockfiles, imports and
  transitive package closure. Treat package identities as source-pinned.
- Deduplicate dependency closures by toolchain/profile/content fingerprint.
  Reuse compiled dependencies read-only; do not mix incompatible profiles.
- Materialize only required source/import closures into a `TemporaryDirectory`
  or remote worker memory-backed filesystem, and run the original Lean
  elaborator/exporter. For projects requiring build scripts or plugins,
  create an isolated execution policy; remote source is untrusted.
- Stream elaborated terms/axiom/dependency receipts to the PostgreSQL world;
  commit records transactionally only after the checker/exporter evidence
  is validated; drop the ephemeral source directory afterwards.
- Apply independent concurrency and memory limits to retrieval, elaboration,
  database writes and proof checking. Each worker must be restartable.
- Preserve repo/revision, original path and declaration, source/proof digests,
  toolchain, dependency closure, compatibility and license metadata.

If source files must **never** reach the local host, run the Lean worker on
remote compute and transmit only verified structured declaration records.
This is a separate deployment/execution capability, not delivered by source
streaming. No Docker or CI dependency is required; Nix-managed ephemeral
workers fit the requested local orchestration model.

### Scale and completeness

The source inventory requires no permanent repository checkout, but a
single giant source blob still occupies bounded temporary memory. Archive
transport may transfer enormous non-Lean content; enforce network, compressed
byte, wall-clock and total uncompressed budgets at the orchestrator.
The archive streamer now enforces compressed transport, per-Lean-file and
aggregate Lean-source byte budgets. Whole-repository content/CPU/wall-clock
budgets still require orchestration, and a tar member expansion attack remains
a concern for other non-Lean entries unless aggregate extracted byte budgets
are separately enforced.

Do not report repository completion when a tree was truncated, source skipped
by a cap, a request failed, or an elaboration import closure was incomplete.
For 21,481 repos compare: REST selective fetch, one-request archive streaming,
and sparse/partial Git object retrieval; select by actual repository size and
module demand. Measure I/O per useful imported Lean declaration.
