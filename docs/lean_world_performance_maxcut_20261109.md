# Lean World throughput and memory gate — independent performance tranche

## 10 November 2026 revised six-gate maximum-cut implementation status

This paragraph supersedes older remarks in this document that the remote streaming tests, migration and worker had no executable test surfaces. **Code/test sources have advanced substantially; the real live services have NOT been tested by this session.**

| Priority | New source implementation | Actual validation standing |
| --- | --- | --- |
| 1. PostgreSQL migration | Repaired SQL escaped newline; immutable occurrence UPDATE and TRUNCATE guards; `tests/test_lean_world_postgres_migration.py` reapplies migration twice in an isolated schema, checks batch INSERT/DELETE counts, composite FK, provenance conflict, keyset and rejected UPDATE/TRUNCATE; `scripts/run_lean_world_pg_ephemeral.sh` starts and cleans a private-socket PG16 instance from the pinned Nix shell | **Not executed here**: this container has no `psql`/`postgres`/`nix`. PostgreSQL 15 syntax for statement transition tables is documented, but actual DB receipt OPEN |
| 2. Streaming + comparative benchmark | Fixed literal escaped-newline syntax in `lean_remote_archive_stream.py`; source callbacks in both archive and REST ingestion; tar uncompressed-byte cap now counts ALL regular members (including non-Lean); callback, skipped/oversized, non-Lean archive, digest and malformed negative-control tests; `bench_lean_world_acquisition.py` offline and pinned live modes | **Offline exploratory transport model executed** (below); exact repository test suite and real HTTP latency not executed here |
| 3. No-checkout to world | `lean_world_source_world.py` admits original provenance receipts, verifies original Git blob/SHA256 bytes and forwards verified bounded source to a consumer; `run_lean_world_no_checkout.py` wires both actual acquisition paths to source-world output and optional Lean worker | Source world **implemented**, no real remote acquisition run; it never treats source hashes as elaborated proof terms |
| 4. Ephemeral Nix Lean worker | Existing `flake.nix` reused via `devShells.lean-world` without changing Agda shell; `lean_ephemeral_elaboration.py` materializes one temporary source at a time, hashes actual compiled OLean dependency directory and `flake.lock`, uses atomic content-addressed OLean receipt/cache, sanitizes subprocess environment; mock tests + `smoke_lean_ephemeral_real.py` | Real pinned Nix Lean compiler/cache smoke **not run** in this container; no exporter or kernel-certified declaration receipts |
| 5. DAG/fibre/hyperfabric | `lean_world_canonical_dag.py` exact canonical byte-equality after hash lookup, preserved independent proof/source occurrences, exporter-supplied acyclic dependency graph, generation-pinned bounded keyset fibre search and context-indexed dependency incidence with truncation; compatibility with actual PR #1483 `FibreIndex`; `run_lean_world_export_admission.py` requires complete original source manifest and independent canonical Lean exporter JSONL | Source and tests **authored**, not run here. Projection fibre is NOT equivalence, source ingestion is NOT elaboration, and source-given dependency edges are NOT new proven gluing |
| 6. Representative source-to-world performance | `bench_lean_world_acquisition.py` measures original verified source bytes through the real no-checkout source-world builder (network bytes/requests, wall, source count, traced peak bytes); `bench_lean_world_corpus.py` requires 3 distinct pinned repository classes and archive/REST exact coverage agreement | **Real representative corpus measurement OPEN**: no permitted network/runtime here. Peak PostgreSQL storage, actual Lean elaboration time, and full source→elaborated world throughput remain separately OPEN |

### Local no-CI execution in the existing flake

```bash
nix develop .#lean-world --command bash scripts/run_lean_world_maxcut_local.sh offline
nix develop .#lean-world --command bash scripts/run_lean_world_maxcut_local.sh postgres
nix develop .#lean-world --command bash scripts/run_lean_world_maxcut_local.sh lean
nix develop .#lean-world --command bash scripts/run_lean_world_maxcut_local.sh corpus pinned-repositories.json
```

The corpus manifest must supply **exact 40-hex commit IDs** for distinct small/medium/large Lean repositories; moving branches and inferred revision IDs are rejected. No Docker or CI required. For direct acquisition use `scripts/run_lean_world_no_checkout.py OWNER/REPO SHA --transport archive|rest`. Opt-in `--compile --flake . --cache DIR --closure-digest 64HEX` invokes the ephemeral worker; a successful compilation is explicitly marked `lean-compiled-not-exported`. Use `scripts/run_lean_world_export_admission.py --sources source.jsonl --exports exporter.jsonl [--index-path PR1483/scripts/lean_world_fibre_index.py]` only with independent original Lean exporter output. No source-only rows are promoted to theorem facts.

### Independent exploratory local transport-model measurements (NOT PR exact-code or remote benchmarks)

A small standalone Python transport model was actually executed in this container for the same synthetic 1 KiB Lean-source payloads, 3 repeated runs, no network latency and highly compressible repeated bytes:

| Files | Archive median / compressed bytes | REST JSON/base64 median / bytes | Network HTTP requests |
| ---: | ---: | ---: | --- |
| 100 | 0.0065 s / 1,335 B | 0.0018 s / 149,800 B | archive 1 / REST 101 |
| 1,000 | 0.0923 s / 11,715 B | 0.0176 s / 1,498,000 B | archive 1 / REST 1,001 |
| 3,000 | 0.2992 s / 34,850 B | 0.0605 s / 4,494,000 B | archive 1 / REST 3,001 |

Archive reduces simulated transfer dramatically on these trivially compressible sources; in-memory JSON/base64 processing was faster in this local model. **No remote call, PostgreSQL, Lean elaboration, or actual repository implementation is measured by those figures.** Do not extrapolate the measured ratios to real GitHub/Lean repositories.

### Strict highest-alpha unpaid receipts

1. **PG01** Execute `run_lean_world_pg_ephemeral.sh` under pinned Nix and preserve exact real server version, migrations, count/concurrency/index-plan receipts (the current harness does not yet test concurrent admission).
2. **STREAM01** Run entire exact-head offline suite and pinned live REST/archive benchmark; measure actual failed/skipped coverage, network latency and compression over representative sources.
3. **WORLD01** Feed real source bytes into the existing production world builder/validated Lean exporter; source-world manifests and optional PR #1483 index adapter are not yet a kernel-term exporter.
4. **LEAN01** Run the actual pinned Lean smoke, build/reuse a representative compiled dependency closure, and validate an exporter for typed canonical terms/dependencies; no proof equivalence without kernel receipts.
5. **DAG01** Persist canonical nodes/edges into the intended PostgreSQL world, test duplicate/conflicting producers/concurrency, and validate source-to-exporter provenance and full hyperfabric commuting maps (the current context incidence view makes no gluing theorem).
6. **PERF01–06** Run 3+ exact-pinned corpus inputs end-to-end through elaboration and PostgreSQL; record p50/p95/p99, throughput, peak RSS/disk, typed-declaration count and incomplete/failed receipts by stage.



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

## 11 November — candidate DAG PostgreSQL implementation (NOT kernel admission)

Added `scripts/sql/lean_world_candidate_dag_v1.sql`,
`scripts/lean_world_postgres_candidate.py`, and
`tests/test_lean_world_postgres_candidate.py`.

The writer consumes ONLY a sealed existing `CanonicalLeanWorld` (never source
text), persists the exact-type statement interners and source-original proof
occurrences into the existing `lean_world_fibre`/`statement`/`occurrence`
tables, and adds immutable candidate source receipts and original dependency
edges through foreign keys. One psycopg3 transaction covers the complete
batch. Locked fibre rows serialize same-profile/type admission and exact bytes
are compared even after matching SHA-256; original occurrence/provenance and
dependency conflicts abort the transaction. Repeat admissions are idempotent.
There is no signed checker attestation and the schema intentionally permits
ONLY `candidate-unverified`, never proof certification.

Validation supplied by the operator before this tranche: #1484 canonical DAG
11/11, PostgreSQL syntax and live temporary-schema migrations (2 tests passed),
and actual Nix Lean 4.28 compilation of pinned Batteries/Tactic/Init.lean
with a missing-Std-import negative control. These do NOT imply the new
candidate writer has passed its own live database tests.

New exact local gate on #1484 (explicit test database only):
```sh
PGDATABASE=<isolated-test-database> python3 -m unittest discover -s tests \
  -p 'test_lean_world_postgres_candidate.py' -v
```
Requires psycopg3. Tests create/drop only their own UUID-named schema, and
exercise an exact statement with two original occurrences, dependencies,
idempotence, provenance conflicts and rollback. Do not point this gate at a
production database without reviewing credentials and access policy.

Remaining P0: independently authenticated native-v3 semantics and complete
pinned environment; conversion of checked native declarations into the
existing canonical type bytes with exact binding; and separately authorized
promotions. Candidate persistence is an infrastructure advancement, not
source-to-world proof certification or reuse.

### Executable candidate-only integration entry point

`scripts/run_lean_world_candidate_pg.py` now connects the existing
`run_lean_world_export_admission.build()` complete source summary / exact
export-row intake to `persist_candidate_world()` and prints an explicit
`candidate-unverified` result. Requires an operator-chosen existing target
schema and explicit PGDATABASE; never silently writes the default public
schema. Schema migrations must be applied within that chosen schema first.

```sh
# Review schema and connection first; no production authority implied.
PGDATABASE=lean_world_test python3 scripts/run_lean_world_candidate_pg.py \
  --sources verified_sources.jsonl \
  --exports externally_exported_candidates.jsonl \
  --schema lean_world_candidate_test \
  --acknowledge-unverified-candidates
```

The existing Nix PostgreSQL ephemeral script now also runs the new
`test_lean_world_postgres_candidate.py` tests, and its devShell adds psycopg3
from pinned nixpkgs. Neither this CLI nor the transaction store can infer
Lean type validity, checker trust, or theorem status from the external rows.

Further required: actual independent native-v3 checker under pinned closure,
authenticated identity-bound term/statement projection, and subsequent
original-proof reuse with an observed Lean kernel receipt.
