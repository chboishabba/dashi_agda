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
3. **H08**: make #1494 spool publication atomic across processes, using temporary files, fsync of files and directory, and atomic rename/no-clobber semantics. Queue readers must never see partial files.
4. **W04–W08**: rebase or port #1483's *retrieval-only* fibre index without promoting profile compatibility to theorem equivalence, and prove/test deduplication and bounded retrieval.
5. **H01 / H06 / K01–K02**: test a real pinned Lean declaration end to end, then a second independent kernel-checked proof using a retrieved donor.
6. **H07 / I01**: test throughput, concurrency, import invalidation, storage amplification and source/attribution retention against real repositories.

## Local acceptance

```sh
python3 -m unittest discover -s tests -p 'test_lean_world_builder_contract.py' -v
```

The tests exercise the contract only. They do not substitute for a Nix Lean run, PostgreSQL admission, actual native-v3 DAG validation, or kernel rechecking.
