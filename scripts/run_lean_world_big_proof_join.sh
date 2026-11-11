#!/usr/bin/env bash
# Ten actual proof joins across Batteries and mathlib4, Lean 4.28.
# No .NET, independent checker, Docker, per-blob REST, CI or source edits.
set -euo pipefail
if [ -z "${PGDATABASE:-}" ]; then
  echo "PGDATABASE must be configured explicitly" >&2
  exit 2
fi
for bin in python3 lean; do
  command -v "$bin" >/dev/null || { echo "MISSING: $bin" >&2; exit 2; }
done

out="/tmp/dashi-big-proof-join"
if [ "$#" -ge 1 ]; then out="$1"; fi
mkdir -p "$out"
schema="lean_world_source_pilot"
if [ -n "${DASHI_WORLD_SCHEMA:-}" ]; then schema="$DASHI_WORLD_SCHEMA"; fi
batteries_revision="495c008c3e3f4fb4256ff5582ddb3abf3198026f"
mathlib_revision="8f9d9cff6bd728b17a24e163c9402775d9e6a365"

export DASHI_LEAN_BIN="$(command -v lean)"
python3 -m unittest discover -s tests \
  -p 'test_lean_world_join_proofs.py' -v
python3 -m unittest discover -s tests \
  -p 'test_lean_world_cross_repo_joins.py' -v
python3 -m unittest discover -s tests \
  -p 'test_lean_world_compiled_join_store_pg.py' -v

# Each compatible revision is a DISTINCT pinned original source snapshot.
# Prior three-repository objects and provenance remain unchanged.
python3 scripts/run_lean_world_stream_pg.py \
  leanprover-community/batteries "$batteries_revision" --schema "$schema"
python3 scripts/run_lean_world_stream_pg.py \
  leanprover-community/mathlib4 "$mathlib_revision" --schema "$schema"

python3 scripts/run_lean_world_join_proofs.py \
  --schema "$schema" \
  --repository leanprover-community/batteries \
  --revision "$batteries_revision" \
  --module Batteries.Data.List.Basic \
  --donor List.replaceF_eq_replaceFTR \
  --donor List.splitOnP_eq_splitOnPTR \
  --donor List.takeD_zero \
  --donor List.takeD_succ \
  --donor List.takeD_nil \
  --max-modules 512 \
  --max-source-bytes 134217728 \
  --timeout 600 \
  --lean "$(command -v lean)" \
  --persist-joins \
  --output "$out/batteries-five-theorem-joins.json"

# Cross-repo theorem composition: FOUR mathlib proofs and ONE Batteries proof.
python3 scripts/run_lean_world_join_proofs.py \
  --schema "$schema" \
  --repository leanprover-community/mathlib4 \
  --revision "$mathlib_revision" \
  --additional-source "leanprover-community/batteries@$batteries_revision" \
  --module Mathlib.Logic.Basic \
  --import-module Batteries.Data.List.Basic \
  --donor congr_heq \
  --donor congr_arg_heq \
  --donor List.takeD_zero \
  --donor eq_iff_eq_cancel_left \
  --donor eq_iff_eq_cancel_right \
  --max-modules 1024 \
  --max-source-bytes 268435456 \
  --timeout 600 \
  --lean "$(command -v lean)" \
  --persist-joins \
  --output "$out/mathlib-five-theorem-cross-repo-joins.json"

# Restore BOTH original full compiled import closures from PostgreSQL and
# elaborate second-stage theorem references using the stored .olean objects.
batteries_batch="$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["persistent_join"]["batch_sha256"])' "$out/batteries-five-theorem-joins.json")"
mathlib_batch="$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["persistent_join"]["batch_sha256"])' "$out/mathlib-five-theorem-cross-repo-joins.json")"
python3 scripts/run_lean_world_join_get.py \
  --schema "$schema" --batch "$batteries_batch" \
  --output-dir "$out/batteries-from-db" \
  --lean "$(command -v lean)" --reuse-count 5
python3 scripts/run_lean_world_join_get.py \
  --schema "$schema" --batch "$mathlib_batch" \
  --output-dir "$out/mathlib-from-db" \
  --lean "$(command -v lean)" --reuse-count 5

echo "BIG_JOIN_COMPLETE: 10 source-original theorems compiled and 10 more rechecked from stored PostgreSQL OLean closures"
echo "Receipts: $out/batteries-five-theorem-joins.json"
echo "          $out/mathlib-five-theorem-cross-repo-joins.json"
