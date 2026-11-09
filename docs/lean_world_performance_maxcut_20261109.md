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
