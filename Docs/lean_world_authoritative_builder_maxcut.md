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

## Next tranche — pinned checker execution (observational, not certification)

`scripts/lean_world_external_checker.py` now accepts the existing immutable
`PendingExport`, checks its exact NDJSON bytes, pins the checker executable
to an operator-supplied SHA-256, invokes that checker with no shell or
ambient secret-bearing environment, sets a POSIX output-file size limit,
rejects nonzero exit/timeout/output excess/artifact mutation, and returns
`ExternalCheckReceipt` with executable, original artifact, stdout and stderr
digests. Seven offline tests cover acceptance as an observation and the
critical false-promotion/negative-control cases.

This deliberately does **not** convert checker exit zero into
`BuilderResult.dag_validated`, `world_admitted` or `kernel_certified`.
The binary hash does not authenticate the provenance of the executable or its
transitive Nix closure. A trusted operator must separately pin the entire
checker derivation, attest its checking semantics, account for axioms and
unsafe assumptions, and validate results against real native-v3 fixtures.

Candidate upstream to evaluate: Tenet, which documents checking
lean4export 3.x NDJSON, including 3.0/3.1. This is a source-discovery
candidate, **not a validated DASHI checker**. See
https://github.com/keithadler/tenet . Do not add a second world store.
Reuse #1484's `lean_world_canonical_dag.py` and source-world owners,
and #1483's exact fibre-index adapter once semantic validation is paid.

Local offline commands (run against exact committed branches, no CI):
```sh
python3 -m unittest discover -s tests -p 'test_lean_world_external_checker.py' -v
python3 -m unittest discover -s tests -p 'test_lean_world_builder_contract.py' -v
```
`#1484` separately repaired the malformed PL/pgSQL dollar delimiters in
both receipt-immutability trigger functions and added an offline regression.
Its canonical DAG `seal()` now uses iterative shared-child-safe DFS and has
deep-chain/cycle/diamond regression tests. Those source changes are on
#1484, not yet ancestors of this #1495 stack. No exact-head operator execution
or PostgreSQL migration receipt is claimed.

## P0 dependency update — canonical candidate PostgreSQL writer on #1484

#1484 has progressed beyond the earlier generic metadata-only migration:
`scripts/lean_world_postgres_candidate.py` consumes its **sealed original**
`CanonicalLeanWorld`, writes exact-type interned statements, original source
occurrences and foreign-keyed dependencies under one PostgreSQL transaction,
and checks idempotence and conflict histories. Additional candidate receipt
and edge tables are append-only; psycopg3 is supplied via the pinned Nix shell.
`run_lean_world_candidate_pg.py` joins the existing complete-source
`run_lean_world_export_admission.build` to that writer, requiring an explicit
database, existing schema and candidate-only acknowledgement. Tests cover
rollback, dependency conflict, duplicate receipts and mutating provenance.

This is **unverified candidate persistence** only. #1484 is still a parallel
PR, not an ancestor of #1495, and no new operator execution receipt is claimed.
The next genuine cut is independent Lean native-v3 checker authentication,
complete exported declaration/dependency closure validation, a checked-typed
mapping into those canonical bytes, and real original-donor proof reuse.

The actual lean4export format is documented at:
https://github.com/leanprover/lean4export/blob/master/format_ndjson.md
Tenet documents `tenet check FILE` and `--fail-on-axiom NAME`:
https://github.com/keithadler/tenet
Do not assume Lean 4.28.0's built-in checker has a later command-line mode;
test exact pinned binaries before setting any authority flag.

## End-to-end candidate-checker observation command (still NOT a proof)

`scripts/run_lean_world_native_check_observation.py` now joins the existing
export receipt, #1494 immutable native queue, #1495 PendingExport identity
contract, and pinned checker runner. It invokes `check --fail-on-axiom sorryAx`
against the exact staged native export, and on exit zero publishes an immutable,
content-addressed **observation only**. It never creates `BuilderResult`,
kernel certification, PostgreSQL world admission or an Agda/Lean proof.

```sh
python3 scripts/run_lean_world_native_check_observation.py \
  --native-receipt path/to/native-export-receipt.json \
  --spool path/to/private-immutable-spool \
  --checker-bin /nix/store/.../bin/tenet \
  --checker-sha256 <actual-pinned-executable-sha256>
```

The checker binary path/hash are deliberately operator-provided, not invented
and not downloaded by this command. The binary's exact Nix closure and checker
semantics still need independent policy review. Test-only executable success
is expressly NOT mathematical evidence. Run:
```sh
python3 -m unittest discover -s tests -p \
  'test_lean_world_native_check_observation.py' -v
```
These three new regressions are authored but no live exact-head run was
observed here. Passing the test only shows dataflow and fail-closed status.

## 11 November — runnable pinned real-semantic maximum-cut acceptance

The new files `scripts/lean_world_native_v3_projection.py` and
`scripts/run_lean_world_native_v3_projection.py` consume the official
lean4export 3.x name/universe/expression/declaration records, resolve their
integer references, and produce exact selected-type and proof-term structural
digests with direct named constant dependencies. Mutual inductive groups are
inspected conservatively but **not** independently projected or treated as
certified. A type projection receipt remains `kernel_certified=false`.

The main real acceptance gate is
`scripts/run_lean_world_real_semantic_acceptance.py`. It uses the committed
`Donor.lean` and `Consumer.lean` original fixtures, both checked against
the local HEAD Git objects. It clones and builds upstream tools in a temporary
directory at the following **full immutable source commits**:

- lean4export `v4.28.0` at
  `d065b0009aed0520e9e99752847a33b337661690`;
- Tenet `v0.11.3` at
  `026a35ce8c433b4785a8be8ae15952803ddfacc5`.

It requires Nix-resolved Lean **4.28.0**, `lake`, `git`, and .NET SDK 10
(`dotnet --version` must start with `10.`). It compiles original donor
and consumer Lean modules independently, exports both exact declaration
environments using the pinned exporter, checks both with Tenet while rejecting
`sorryAx`, and REQUIRES a rejection of a pinned negative corpus file. Exact
source, .olean, exporter, checker source/assembly, native export and output
digests are recorded. Temporary tool checkouts are deleted on exit.

Run from an isolated worktree at the committed #1495 head:
```sh
python3 -m unittest discover -s tests -p 'test_lean_world_native_v3_projection*.py' -v
python3 -m unittest discover -s tests -p 'test_lean_world_external_checker.py' -v
python3 -m unittest discover -s tests -p 'test_lean_world_native_check_observation.py' -v
# Run inside the original Nix Lean environment, with .NET SDK 10 available:
python3 scripts/run_lean_world_real_semantic_acceptance.py \
  --output-dir /tmp/dashi-lean-semantic-original
```

The last command writes one immutable `*.semantic-acceptance.json` as the
manifest, plus matching `*.source-world.jsonl` and
`*.candidate-world.jsonl` files. The exact output receipt path is printed.

**Cross-PR maximum cut:** on #1484, the new
`scripts/run_lean_world_semantic_full_acceptance.py` takes that receipt,
the two exact #1495 fixture paths and the pinned `lean` binary, builds the
original canonical DAG, writes its candidate declarations transactionally in
a fresh UUID-named PostgreSQL schema, retrieves the donor, regenerates the
exact original consumer, kernel-elaborates it, and drops the temporary schema.
See #1484's performance/max-cut roadmap for the invocation.

A successful run supports `independent_checker_observed`,
`candidate_fibre_retrieved` and `consumer_lean_elaborated`, **not**
`world_admitted` or a generally authenticated permanent theorem ledger.
External checker/build-chain trust, general native-v3 coverage, source-owner
attribution for arbitrary imports, and general Agda-to-Lean/fibre reuse remain
separate obligations. The new tests and acceptance scripts have NOT been
executed in the operator environment for these new commits.

## 11 November — Rust checker replaces the .NET acceptance dependency

The active acceptance checker is now **nanoda 0.4.13**, implemented in Rust,
from the original pinned commit
`418320295890faed83a96fd97907b12a3b6728c2`
(https://github.com/ammkrn/nanoda_lib). The preceding Tenet/.NET
instructions are **superseded** for the runnable max-cut path; neither .NET
nor C# is a required component.

`scripts/run_lean_world_real_semantic_acceptance.py` checks out nanoda at
the exact immutable Git SHA into a temporary directory, builds
`cargo build --release --locked --bin nanoda_bin`, and launches nanoda via
its documented JSON configuration-file interface. The checker only permits
`propext`, `Classical.choice`, `Quot.sound`, and
`Lean.trustCompiler`; it never permits `sorryAx`, and
`unsafe_permit_all_axioms=false`. Unpermitted declarations may be skipped
but any proof depending on them must fail. It requires a visible positive
checker result and a negative result when a selected theorem's proof
expression is replaced with its type expression in an otherwise
well-formed native-v3 export.

`scripts/lean_world_external_checker.py` also supports
`check_native_export_nanoda`, and the CLI handoff
`run_lean_world_native_check_observation.py` invokes that Rust-specific
interface. The original generic subprocess checker helper remains
available for compatibility tests but is not the preferred admission path.

The `devShells.lean-world` Nix shell now provides `pkgs.rustc` and
`pkgs.cargo` from pinned nixpkgs, with no .NET SDK. Source and Cargo.lock
are pinned; the exact compiled binary digest is included in observations.
No system-wide toolchain change, Docker, or CI is needed.

On an isolated #1495 checkout, run:

```sh
nix develop .#lean-world --command bash \
  scripts/run_lean_world_semantic_maxcut_local.sh \
  /tmp/dashi-lean-semantic-original
```

The downstream #1484 PostgreSQL evidence bridge rejects receipts without
the exact pinned Rust checker identity and explicit no-sorry axiom policy.
The two PRs must remain on their own isolated heads for cross-branch
integration.

**Source-authored, not yet re-executed for this Rust switch.**
Do not claim a successful independent checker or second-proof run before
obtaining real output at the current head. The independent kernel and
general semantic-world admission gates remain logically separate.


## 2026-11-12: read-only same-export JMD / Rust / native-v3 cross-PR cut

Source-written on PR #1495 (not kernel or operator accepted): scripts/lean_world_cross_pr_observation_join.py and tests/test_lean_world_cross_pr_observation_join.py.

**Source discovery correction:** Sibling PR #1484 now contains scripts/lean_world_jmd_native_owner_readonly.py, using the existing dashi_lean4 PR #105 JMD build_jmd_lean_ast_world.py parser's nodes_from_export/reachable/expression_fingerprint. That owner performs only source-read-only structural observation; its independent source is not an ancestor of #1495, and it neither operates the authoritative shared-world builder nor writes the PostgreSQL ledger. The older generic "cannot find JMD parser" blocker has therefore narrowed to exact-head source alignment, independent checker/semantic authority and original world admission.

**Implemented:** A strict source-correlation adapter reads #1494's original immutable handoff through the existing PendingExport parser. It checks source closure, repository, revision, module, declaration and toolchain against the original native-v3 observation; recomputes the exact exported type and proof bytes, alpha-type candidate digest, original dependency names and source selection from the actual native export, not the supplied projection JSON. It requires a content-addressed, canonical Rust-nanoda observation tied to the identical original artifact SHA and handoff key, always as an uncertified process observation. It optionally correlates a separately SHA256-pinned JMD read-only output with the identical native export, original Lean githash, declaration, direct type/proof constants, and independently pinned JMD source SHA. It neither imports sibling branches nor copies JMD's SQLite world.

All output always has native_dag_complete=false, imported_dependencies_resolved=false, checker_semantics_authenticated=false, builder_authority_authenticated=false, candidate_admission_authorized=false, world_admitted=false and kernel_certified=false. The output is an immutable content-addressed observation; no source parser, signed receipt, cross-repository provenance string, or executable exit status is accepted as a theorem.

**Adversarial tests:** synthetic same-export idempotence/nonpromotion, mismatched revision, rehashed fake type bytes, altered source closure, checker artifact/policy and forbidden promotion, out-of-spool and symlink rejection, positive synthetic JMD correlation and negative JMD source/revision/dependency/export pins. A fabricated checker receipt is deliberately permitted only as a *non-authoritative observation*; these tests cannot certify nanoda/Lean.

Exact local commands on isolated #1495 head, with no CI dependency:

    python3 -m unittest discover -s tests -p 'test_lean_world_cross_pr_observation_join.py' -v
    python3 -m unittest discover -s tests -p 'test_lean_world_native_p1_codec.py' -v
    python3 -m unittest discover -s tests -p 'test_lean_world_native_v3_projection*.py' -v

**Exact remaining max-cut:**
1. Obtain and execute the genuinely pinned Rust nanoda + Lean 4.28 + lean4export native-v3 donor/consumer positive and corrupt-proof negative controls on #1495 in the original Nix shell; validate exact checker toolchain closure and axiom policy. NO receipt in this turn.
2. Execute the sibling #1484 read-only JMD owner against the same original export with the authentic PR #105 source hash; pin the bytes/observation before using this cross-PR join.
3. Source-preservingly reconcile #1484 candidate DAG/PG/fibre with #1495 native-v3 source/independent checker, run exact original Lean donor retrieval and independently elaborated consumer under ephemeral PostgreSQL.
4. Supply actual, authenticated dependency-closure, checker/builder and original world-admission authorities before promoting any proof or persistence status. Agda↔Lean formal semantic transport, YM physical source, Bishop analytic/Koenigs, RH, BSD, global Kneser and P!=NP are mathematically independent remaining gates.

All new code is SOURCE-WRITTEN: no local exact-head test or kernel receipt is claimed. Use local source-backed verification, not CI status, as authority.


### Exact paired observation invocation (still no world admission)

Sibling #1484 now has an immutable native/JMD observation producer at scripts/run_lean_world_jmd_readonly_observation.py. It requires the true original JMD PR #105 source SHA, selected native export SHA and a private spool; its output includes an independent observation SHA.

The #1495 consumer takes the literal existing #1494 handoff manifest, already published #1495 type projection, independently observed pinned nanoda result, and optionally that #1484 JMD result:

    python3 scripts/lean_world_cross_pr_observation_join.py \
      --manifest /path/to/sha256.json \
      --projection /path/to/sha256.native-type-observation.json \
      --checker-observation /path/to/sha256.checker-observation.json \
      --spool /path/to/private/immutable-spool \
      --jmd-observation /path/to/pinned/jmd-result.json \
      --jmd-sha256 ACTUAL_JMD_RESULT_SHA256 \
      --jmd-source-sha256 ACTUAL_PINNED_JMD_PR105_SOURCE_SHA256

This output is necessarily same-native-export-correlated-uncertified, with no proof/DB status promotion. A synthetically forged checker JSON can test binding but cannot authenticate the underlying Rust executable or Lean proof. The independent checker run, original native dependency validation, completed DAG and PostgreSQL world-admission API remain the active high-alpha gates.
