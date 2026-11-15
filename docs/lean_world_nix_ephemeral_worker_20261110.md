# Lean World — Nix-managed ephemeral elaboration tranche

## Reuse rather than duplicate

The checked-in DASHI Nix authority is `flake.nix` / `flake.lock`.
The checked-in Agda worker is
`scripts/run_agda29_parallel_check.sh`, with resource guards, cache
reuse, optional ephemeral source trees and a separate authoritative Agda
track. A root `parallel_runner.sh` was **not present on the verified
default-branch GitHub tree**; if the operator has an untracked/local
copy, inspect that separately before merging. Do not alter the Agda
flake lock or replace the Agda wrapper.

New `devShells.lean-world` takes Lean, Python, Bash, Git and coreutils
from the **same locked nixpkgs**. It does not pin arbitrary other
projects' Lean version: the worker reads the *remote source's*
`lean-toolchain` at the supplied 40-character commit and fails if the
shell's Lean executable does not match. Reproducibility is a conjunction
of Nix lock, source revision, original Lean toolchain, and dependency
closure, never one pin alone.

## First working path (trusted repositories only)

```bash
# With an appropriate repo whose lean-toolchain matches nixpkgs lean4:
bash scripts/run_lean_world_nix.sh owner/repo FULL_40_HEX_SHA Src/Target.lean
# Output: one JSON receipt, source hashes and check status.
```

The wrapper uses `nix develop .#lean-world --no-update-lock-file --command`;
the Python worker fetches a pinned tree and only selected source/import
blobs, stages them in `TemporaryDirectory`, typechecks with Lean and
deletes the workspace including generated .olean files. It does not
need a local Git checkout, `lake update`, a persistent source tree or
a CI agent. `LEAN_PATH` is constructed from the ephemeral root and
an optional explicitly supplied compiled dependency location.

Use `--timeout`, `--memory-mib` and the source-count/byte limits;
stdout is a machine-readable JSON receipt, not a proof certificate.
The subprocess limit is Linux/POSIX-specific; do not run as a security
sandbox for hostile sources. Lean elaborators and imported macros can
execute code: untrusted repositories need an independent remote
sandbox/execution boundary before being admitted at scale.

## Implemented boundary

- Exact repository/commit pin plus Git blob identity checking.
- `lean-toolchain` format + observed Lean version equality, fail closed.
- Recursive same-repository import closure for ordinary `import` syntax.
- Explicit caller-supplied external dependency-closure ID and `LEAN_PATH`
  required for non-builtin imports outside the pinned repo.
- Bounded temporary source count/bytes, memory and wall-clock time.
- JSON source hash/provenance records and `lean-module-checked` only
  if Lean exits zero and emits .olean. No declaration AST is claimed.
- No checkout remains, including after unsuccessful check.
- Offline tests for closure, pin/version mismatch, bad imports, external
  dependency admission, ephemeral cleanup and receipt boundaries.

**No tests or real Nix Lean compilation were run through the connector.**
The scripts have not yet been measured on real corpus samples. The
PostgreSQL migration in PR #1484 also still requires rerunning psql
after correction.

## Exact remaining cut

| Gate | Current boundary | Needed to close |
| --- | --- | --- |
| N01 | Reuse Nix shell source | Run `nix develop .#lean-world` on operator machine and record flake.lock / Lean version |
| N02 | Selective module/manifest fetch | Support complete pinned Lake project, package resolution, and source/build configurations |
| N03 | External dependency cache | Build and attest version-matched read-only Nix/store or content-addressed .olean closures; do not accept user-provided labels as proof |
| N04 | Full source coverage | Handle scripts/plugins/generated modules, nonstandard imports, submodules, Lean 3 and other unsupported profiles explicitly |
| N05 | Kernel term export | Run a real Lean environment exporter with axiom/universe/dependency records, not just .olean creation |
| N06 | PostgreSQL intake | Transactionally ingest exported declarations into statement DAG, fibre, proof-occurrence and provenance tables |
| N07 | Worker isolation | Execute untrusted repo builds in sandboxed remote compute; reject source-level code execution on host |
| N08 | Scale/operability | Profile network, elaboration, cache reuse, p95/p99, RSS, disk peak, and checkpointed resumability |
| N09 | Invalidation | Reuse dependencies by content closure, invalidate only affected fibres and imports |
| N10 | Proof payment | Match original DASHI obligations via AO and check real implications in the appropriate kernels |

The core proof boundary remains unchanged: same-fibre proximity is a
candidate-retrieval signal, never logical equivalence or a discharged
mathematical obligation. We need checked transport/equivalence receipts
before merging mathematical identities.


## PR #1491 follow-up corrections (2026-11-11)

Validation of the earlier head found 18 passing tests and 2 failures.
- Non-Lean tree blobs are now excluded before applying Lean-source SHA/size validation; malformed `.lean` entries continue to fail closed.
- Import discovery now recognizes `import`, `public import` and `protected import`. Within the supported simple-import fragment, the worker stages same-repository dependencies and compiles their `.olean` artifacts before the selected target.
- The Nix wrapper now explicitly resolves `.#lean-world-bin` through `nix build --no-link --print-out-paths` using the existing flake lock and passes its absolute `/nix/store/.../bin/lean` to Python. There is **no system-Lean PATH fallback from this wrapper**.
- Added regression tests for the two failures and compilation ordering.

These changes are source-written on this PR branch; the operator still needs to rerun the isolated tests, `nix develop` realization and one pinned Batteries revision. The flake's Lean version may differ from Batteries' pinned `lean-toolchain`: correct behaviour is refusal, not executing Arch Lean. Building arbitrary Lake packages and a cross-repo reusable compiled dependency cache remain separate unpaid gates.


## 11 November 2026 — Native v3 AST exporter and compiled closure cache (PR #1491)

The zero-checkout ephemeral worker now provides an **opt-in, pinned native
Lean AST export stage**, not just a successful `.olean` compilation:

- `scripts/lean_world_native_v3_export.py`: calls an actual
  `lean4export` executable with a selected module/declaration before
  `TemporaryDirectory` cleanup. Validates the NDJSON v3 envelope,
  requires a declaration record, limits bytes and execution resources,
  and retains the exact native bytes at a SHA-256 content address.
- `scripts/lean_world_compiled_local_closure.py`: topologically builds
  same-repository local imports, keyed by original repository+Git commit,
  exact source SHA-256 list, observed Lean version, target and declared
  external dependency closure. Cache entries retain individual olean
  content hashes and are checked before reuse. Its cached dependencies
  are copied to the temporary workspace; the target module is still
  compiled by the existing Lean checker.
- `scripts/lean_ephemeral_nix_worker.py`: invokes these operations within
  the same ephemeral source workspace using
  `--compile-local-imports --compiled-cache-dir` and
  `--native-declaration --native-out --export-bin`. The original
  zero-export checker mode still exists. Its compiler environment now
  excludes unrelated credentials before launching untrusted Lean code.
- Companion consumer:
  `dashi_lean4/scripts/jmd_lean_ephemeral_ast_handoff.py` on PR #105
  checks the original worker/source receipts, native artifact digest and
  repository/commit agreement and emits a v3 exporter manifest row
  accepted by the **existing**
  `scripts/build_jmd_lean_ast_world.py`.

Illustrative execution for an explicitly trusted, pinned repository with
a compatible Nix-managed Lean compiler and compatible `lean4export`:

```sh
bash scripts/run_lean_world_nix.sh owner/repository FULL_40_HEX_SHA Target.lean \
  --compile-local-imports \
  --compiled-cache-dir /path/to/lean-olean-cache \
  --native-declaration Existing.Namespace.theorem \
  --native-out /path/to/native-artifacts \
  --export-bin /path/to/version-matched/lean4export \
  > /tmp/native-worker-receipt.json

# From dashi_lean4 PR #105:
python scripts/jmd_lean_ephemeral_ast_handoff.py \
  --receipt /tmp/native-worker-receipt.json \
  --github-id ORIGINAL_NUMERIC_GITHUB_REPO_ID \
  --manifest-out /tmp/native-export-manifest.jsonl

# Existing native v3 DAG parser/SQLite world owner:
python scripts/build_jmd_lean_ast_world.py \
  --database ../dashi_agda/.dashi/repository.sqlite3 \
  --repositories docs/roadmap/jmd_lean_corpus/github_lean_repositories.csv \
  --exports /tmp/native-export-manifest.jsonl
```

This is **not a claim that `lean4export` is installed by the current
`lean-world` Nix shell**, or that an arbitrary repository can be
compiled with the single-module worker. Correct full Lake/package
closure construction, version-pinned external dependency materialisation,
and sandboxing arbitrary third-party macros remain explicit gates.
The worker accepts only a selected named declaration for native export,
not complete generated-declaration coverage.

**Verification boundary:** the native exporter initially verifies v3
syntax, record count and content hash. The separate canonical importer
must still verify its complete name/universe/expression DAG and
declaration roots before *any* AST world admission. Even that admission
is **not** Lean kernel proof certification or mathematical equivalence.
The new cache and export modules have synthetic offline local
regressions; no real Nix/Lean/PostgreSQL end-to-end run was possible in
this session.

### Revised specific gates

| Gate | Source status | Unpaid physical acceptance |
|---|---|---|
| N03-local | Source-hash-keyed local compiled import cache integrated | Real cache reuse with a pinned Lean toolchain; external package closure not automatically constructed |
| N05-selected | Real `lean4export` invocation and durable native v3 artifact capture integrated | One actual toolchain-matched export; full module/environment enumeration remains open |
| N05-DAG | Existing PR #105 v3 importer receives manifest through strict handoff | Real full DAG acceptance and declaration/source provenance check |
| N06 | Canonical SQLite world path reused | PostgreSQL canonical-world admission and psql migration retest remain open |
| N07 | Compiler environment secrets reduced | Isolated execution sandbox still required for unattended untrusted corpus |
| N08 | Source-coded bounded cache/export pathway | Actual throughput, memory and cache hit measurements remain open |
| N10 | No proof promotion from native AST export | First real original DASHI gap and kernel-checked implication remain open |
