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
