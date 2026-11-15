# Lean world — native v3 exporter → authoritative validator handoff

This tranche follows PR #1491 at `d86e748c`. It does NOT implement a second
Lean AST world and deliberately does not mark anything as a proved theorem.

`scripts/lean_world_native_admission_queue.py` accepts the
`native_export` object emitted by the ephemeral worker. It checks:
- original repository, immutable revision, module, declaration and closure hashes
- native export artifact SHA-256, v3 envelope, record/declaration counts
- fail-closed status: `world_admitted=false`, `complete_dag_checked=false`,
  `kernel_proof_certified=false`
- independently observed source/provenance identity and safe paths

It stores one `.ndjson` artifact per content digest and a separate immutable
JSON manifest per source/revision/declaration/dependency-closure identity.
Repeated submissions are idempotent. Different provenance can point at the same
native export without discarding attribution. It keeps **no Git repository checkout**.

```sh
python3 -m unittest discover -s tests -p 'test_lean_world_native_admission_queue.py' -v
python3 scripts/lean_world_native_admission_queue.py \
  /path/to/native-export-receipt.json --spool /persistent/native-v3-spool
```

The operator must save the `native_export` member of the worker receipt as
the input JSON object. This utility is a staging boundary, not a producer
integration switch.

## Exact outstanding maximum cut

- H01: verify actual lean4export v3 stream against the selected original
  Lean revision/toolchain and compiled package closure
- H02: locate and call the **authoritative** JMD builder at its actual source
  branch/path; do not invent a replacement parser
- H03: run complete DAG/reference/typing validation of the exported native
  records and persist a separate checker receipt
- H04: ingest validated nodes into canonical DAG and original world DB, with
  transactionally preserved statement, proof, dependency and attribution records
- H05: reconcile world admission status independently from source/checker
  provenance; never promote stage success into theorem certification
- H06: source-pin AO obligation discovery and demonstrate the first actual
  donor → residual implication → kernel payment
- H07: benchmark ingestion latency, memory, spool bytes, content sharing,
  adversarial collision controls and PostgreSQL write amplification
- H08: establish atomic cross-process insertion or transactional locking for
  concurrent spool writers (current O_EXCL is idempotent for completed writes
  but not a durability/visibility protocol for readers during concurrent writes)

Local standalone regression on authored code: 8 tests passed. Full PR #1491
regression and real Nix/Lean/PostgreSQL integration remain operator validation.
