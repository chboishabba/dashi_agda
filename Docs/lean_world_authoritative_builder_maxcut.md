# Lean world authoritative builder — maximum-cut contract

Status: **interface only**, stacked on PR #1494 at `a3e0e9cfdcce8bc3aa6c1a0a31fd2f90f8b2bedd`.

## Roadmap reconciliation

- `.planning/ROADMAP.md` covers the older Agda geometry/MDL closure phases, **not** the Lean-world pipeline.
- PR #1483 establishes W01–W10 for fibre-index source pinning, exact statement intake, bounded search, attribution, and independent proof payment. **It is not an ancestor** of #1494 and its Python index is not an authoritative DAG builder.
- PR #1494 establishes H01–H08. Its admission queue verifies immutable source/artifact identity, not term references or Lean kernel judgments.

## Implemented here

`scripts/lean_world_builder_contract.py` defines `PendingExport`, `AuthoritativeBuilder.validate`, `BuilderResult`, and read-only shape/binding checks. It validates that a #1494 handoff manifest and content-addressed artifact still agree before invoking any external builder. It rejects mismatched checker outputs, unresolved returned node references and unauthorized queue status promotion.

Nothing here parses native AST records into mathematical nodes, proves typing, independently authenticates validator implementations, writes a world database, or claims theorem certification. A malicious/fake builder can return well-formed fields; that is **not** trusted evidence. This module must not be used as an admission authority by itself.

## Unpaid decisive implementation

1. **H02 / W02–W03**: locate or implement a reviewed authoritative Lean native-v3 parser and DAG validator that resolves every native reference against a complete pinned Lean environment and supplies an independently verifiable checker receipt.
2. **H03–H05**: expose the real builder API, bind each emitted node and dependency to the source closure and validator evidence, and implement transactional PostgreSQL persistence. Only the trusted builder/database transaction may alter admission status.
3. **H08 (local POSIX implementation added)**: immutable spool publication now uses private temporary files, file/directory fsync, atomic no-clobber hard links, and conflict detection. Cross-host readers, network filesystem semantics, crash injection and stale temporary-file cleanup remain to validate.
4. **W04–W08**: rebase or port #1483's *retrieval-only* fibre index without promoting profile compatibility to theorem equivalence, and prove/test deduplication and bounded retrieval.
5. **H01 / H06 / K01–K02**: test a real pinned Lean declaration end to end, then a second independent kernel-checked proof using a retrieved donor.
6. **H07 / I01**: test throughput, concurrency, import invalidation, storage amplification and source/attribution retention against real repositories.

## Local acceptance

```sh
python3 -m unittest discover -s tests -p 'test_lean_world_builder_contract.py' -v
```

The tests exercise the contract only. They do not substitute for a Nix Lean run, PostgreSQL admission, actual native-v3 DAG validation, or kernel rechecking.

## Follow-up tranche — immutable spool publication

`scripts/lean_world_atomic_spool.py` supplies the atomic, no-clobber
POSIX publication primitive. The #1494 queue now calls it for both the native
artifact and the manifest. The manifest is published *last*, making it the
reader-visible commit marker. The original queue schema and status remain
unchanged. New tests cover repeated writes, conflicting bytes, pre-existing
partial entries, symlinks and concurrent writers. Integration tests construct
a real queue record then pass it through the read-only builder contract.

The integration boundary accepts an empty dependency-closure ID because the
original #1494 receipt schema explicitly allows it; the source closure remains
required. Empty closure must never be interpreted as evidence of resolution
of external imports.

**No kernel or world-admission status is promoted.** No PostgreSQL writer or
trusted native-v3 DAG validator was introduced.

## Exporter-side H08 follow-through

The original `scripts/lean_world_native_v3_export.py:store_native`
published with `os.replace`, which could overwrite an already-published
content-addressed native export. It now calls the same no-clobber,
fsync-backed immutable publication primitive used by the queue.
`tests/test_lean_world_native_export_atomic.py` covers repeat export,
conflicting bytes under the expected digest name, and symlink rejection.

The exporter specifically identifies
`dashi_lean4/build_jmd_lean_ast_world.py` as its expected DAG validation
owner. A GitHub file lookup on `chboishabba/dashi_lean4` main returned 404
for that exact path, and source search did not locate it there. This is a
**source discovery blocker**, not proof that no implementation exists on other
branches or in another repository. No replacement native-v3 graph semantics
have been invented in this tranche.

## 11 November follow-through — actual prior canonicalization owner

Live PR inspection established that #1484 (head `c4bca43ed5e46795dde1f439c1f4df821337fd9a`) includes `scripts/lean_world_canonical_dag.py` and `scripts/lean_world_source_world.py`. The former already owns exact canonical-type interning under profile, original source/proof occurrence retention, explicit dependency completeness and cycle rejection, context-indexed incidence and a read-only adapter to #1483's `FibreIndex`. **Reuse or port these implementations rather than introducing a competing statement identity or hyperfabric store.** They accept elaborated-export rows, however, and neither independently validates native-v3 Lean term typing nor certifies the Lean kernel.

The contract's independent structural guard now rejects duplicate edges, self-dependencies and arbitrary cycles in externally claimed canonical DAGs, using iterative topological traversal. Four additional negative/scale regression tests are authored. This guard is intentionally not proof authentication; neither database admission nor kernel certification follows from its success. Tests have not been run against this exact GitHub branch in the operator's Nix environment.

Updated seam:
1. Port/rebase #1484's exact source receipt and canonical statement interners together with #1483's existing fibre-index adapter into the #1495 dependency stack, preserving independent source occurrences.
2. Supply a genuine native-v3 parser and pinned-Lean checker that verifies declarations, term references, universes, dependency closure and checker receipts. Never infer kernel certification from the exporter envelope or a builder-supplied boolean.
3. Make the checked result feed atomic PostgreSQL canonical admission, then query the persisted fibre index.
4. Retrieve an admitted declaration as donor and kernel-check an independently elaborated consumer proof.
5. Run negative controls, Nix Lean, PostgreSQL rollback/idempotency/concurrency and actual representative corpus benchmarks locally (not CI).
