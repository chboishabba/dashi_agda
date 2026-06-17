# Agent Notes

## Agda And Nix

This repository has its own local `flake.nix` and `flake.lock`. Treat them as
the reproducibility authority for Dashi artifacts and baked references. Do not
update or rewrite the Dashi flake/lock just to get a newer Agda, unless the user
explicitly asks for that migration.

For day-to-day checking, prefer the neighboring Agda checkout at
`/home/c/Documents/code/agda`, which builds Agda 2.9.0 and supports native
parallel import checking via `-j[N]` / `--parallel[=N]`.

The preferred wrapper for this workflow is:

```bash
scripts/run_agda29_parallel_check.sh
scripts/run_agda29_parallel_check.sh DASHI/Core/FormalStructureLawCore.agda
AGDA_JOBS=4 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda
```

The wrapper uses the sibling Agda flake, creates source-only Dashi and writable
standard-library shadows under `/tmp`, defaults to `DASHI/Everything.agda`,
and defaults to `-j8`. Use the expanded command below only when debugging the
wrapper itself or changing the shadow-tree mechanics.

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
repo, run from a temporary source-only shadow tree and use a writable standard
library shadow so Agda can write `.agdai` interfaces.

```bash
AGDA_BIN="$(nix build --no-link --print-out-paths /home/c/Documents/code/agda#debug.bin)/bin/agda"

DASHI_WORK="$(mktemp -d /tmp/dashi-agda29-shadow.XXXXXX)"
STDLIB_WORK="$(mktemp -d /tmp/agda-stdlib-2.3-shadow.XXXXXX)"

rsync -a --prune-empty-dirs \
  --include='*/' \
  --include='*.agda' \
  --include='*.lagda' \
  --include='*.lagda.md' \
  --include='*.lagda.rst' \
  --include='*.lagda.tex' \
  --exclude='*' \
  /home/c/Documents/code/dashi_agda/ "$DASHI_WORK/"

rsync -a /nix/store/pkks1pz1n2bci0pva1sxbydnc4xyliid-standard-library-2.3/ "$STDLIB_WORK/"
chmod -R u+w "$STDLIB_WORK"

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
existing proof/reference hashes. Use the Agda 2.9 path above for faster draft
worker feedback until the project intentionally migrates the baked refs.
