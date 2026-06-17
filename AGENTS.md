# Agent Notes

## Agda And Nix

This repository has its own local `flake.nix` and `flake.lock`. Treat them as
the reproducibility authority for Dashi artifacts and baked references. Do not
update or rewrite the Dashi flake/lock just to get a newer Agda, unless the user
explicitly asks for that migration.

There are two Agda tracks. Keep them separate:

- **Track A, authoritative:** use the Dashi flake/pinned toolchain for final
  `DASHI/Everything.agda` promotion checks. This track preserves baked refs and
  reproducibility, even if it is slower.
- **Track B, draft worker:** use the neighboring Agda checkout at
  `/home/c/Documents/code/agda`, which builds Agda 2.9.0 and supports native
  parallel import checking via `-j[N]` / `--parallel[=N]`. Track B is fast
  feedback only and must not block promotion by itself.

The preferred wrapper for this workflow is:

```bash
scripts/run_agda29_parallel_check.sh
scripts/run_agda29_parallel_check.sh DASHI/Core/FormalStructureLawCore.agda
AGDA_JOBS=4 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda
```

Workers and subagents that are explicitly allowed to run Agda should use that
wrapper, not `agda` directly and not the old `run_agda29_shadow_check` name.
For normal focused checks, this is the command to hand to agents:

```bash
scripts/run_agda29_parallel_check.sh DASHI/Path/To/Target.agda
```

For Python harnesses or sandboxed callers that cannot invoke `nix build`
inside the wrapper, pre-resolve the binary once and pass it through:

```bash
AGDA_BIN="$(nix build --no-link --print-out-paths /home/c/Documents/code/agda#debug.bin)/bin/agda"
AGDA_BIN="$AGDA_BIN" scripts/run_agda29_parallel_check.sh DASHI/Path/To/Target.agda
```

The wrapper uses the sibling Agda flake, creates source-only Dashi and writable
standard-library shadows, defaults to the stdlib `experimental` branch for
Agda 2.9 compatibility, defaults to `DASHI/Everything.agda`, and defaults to
`-j8`. By default the shadow trees are persistent under
`${XDG_CACHE_HOME:-$HOME/.cache}/dashi-agda29` so Agda can reuse `.agdai`
interface files across runs. Use the expanded command below only when debugging
the wrapper itself or changing the shadow-tree mechanics.

Useful cache controls:

```bash
# Cold-cache debug run: delete the persistent shadow and stdlib checkout first.
DASHI_AGDA29_CLEAN=1 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda

# Old throwaway behavior: fresh /tmp shadows removed on exit.
DASHI_AGDA29_EPHEMERAL=1 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda

# Refresh the cached stdlib experimental checkout.
AGDA_STDLIB_UPDATE=1 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda
```

Build or locate the parallel-capable Agda binary with:

```bash
AGDA_BIN="$(nix build --no-link --print-out-paths /home/c/Documents/code/agda#debug.bin)/bin/agda"
"$AGDA_BIN" --version
"$AGDA_BIN" --help | rg 'parallel|-j'
```

Do not use plain `nix run /home/c/Documents/code/agda` for this; the current
Agda flake's default run target can point at a non-bin output.

## Parallel Dashi Checks Without Flake Churn

Agda 2.9 rejects this repository root as a project root because it contains
multiple `.agda-lib` files. To check Dashi with Agda 2.9 without editing the
repo, run from a source-only shadow tree. The wrapper keeps that shadow tree
stable by default because repeated `DASHI/Everything.agda` checks are dominated
by `.agdai` interface rebuilds, not by resolving the Nix Agda binary.

Do not pair Agda 2.9 with released stdlib 2.3 for meaningful results: stdlib
2.3 was tested against Agda 2.7 and 2.8, while native `-j` parallel checking is
new in Agda 2.9. For Track B, use the stdlib `experimental` branch, which
tracks development Agda. Treat failures from this track as best-effort signals
unless Track A also fails.

```bash
AGDA_BIN="$(nix build --no-link --print-out-paths /home/c/Documents/code/agda#debug.bin)/bin/agda"

DASHI_WORK="$(mktemp -d /tmp/dashi-agda29-shadow.XXXXXX)"
STDLIB_WORK="$(mktemp -d /tmp/agda-stdlib-experimental.XXXXXX)"

rsync -a --prune-empty-dirs \
  --include='*/' \
  --include='*.agda' \
  --include='*.lagda' \
  --include='*.lagda.md' \
  --include='*.lagda.rst' \
  --include='*.lagda.tex' \
  --exclude='*' \
  /home/c/Documents/code/dashi_agda/ "$DASHI_WORK/"

rm -rf "$STDLIB_WORK"
git clone --depth=1 --branch experimental \
  https://github.com/agda/agda-stdlib.git "$STDLIB_WORK"

cd "$DASHI_WORK"
"$AGDA_BIN" \
  --no-libraries --no-default-libraries \
  -j8 \
  -i . -i DCHoTT-Agda -i cubical -i "$STDLIB_WORK/src" \
  -WnoUnsupportedIndexedMatch \
  DASHI/Everything.agda
```

Use `-j4` if memory pressure is high. Use `-j8` as the default starting point.
The parallelism is module/import granularity, so it helps most when the import
graph has enough independent modules.

The Dashi flake remains useful for authoritative reproducibility checks and
existing proof/reference hashes. Use Track B for faster draft feedback until
the project intentionally migrates the baked refs. Never let a Track B-only
failure block Dashi math work; verify with Track A before treating a failure as
a real proof obligation.
