#!/usr/bin/env bash
# Cross-PR P1: immutable #1494 handoff -> #1495 exact/alpha Expr codec
# -> #1484's EXISTING PostgreSQL source world, candidate-only.
# Requires REAL pinned native export from an original source revision
# already present in lean_world_source_occurrence.
# No independent checker, CI, .NET, Docker, or second world builder.
set -euo pipefail
for key in PGDATABASE DASHI_WORLD_SCHEMA DASHI_PR1495_WORKTREE \
           DASHI_HANDOFF_MANIFEST DASHI_HANDOFF_DECLARATION DASHI_P1_SPOOL; do
  if ! printenv "$key" | grep -q .; then
    echo "P1 missing required environment variable: $key" >&2
    exit 2
  fi
done
command -v python3 >/dev/null
root="$(pwd -P)"
p1495="$(cd "$DASHI_PR1495_WORKTREE" && pwd -P)"
p1_codec="$p1495/scripts/lean_world_native_p1_codec.py"
test -r "$p1_codec"
test -f "$p1495/scripts/lean_world_native_v3_projection.py"
test -f "$root/scripts/run_lean_world_native_p1_pg.py"
test -f "$DASHI_HANDOFF_MANIFEST"
if [ -e "$DASHI_P1_SPOOL" ]; then
  echo "P1 spool must be a new, non-existing directory" >&2
  exit 2
fi
mkdir -m 700 "$DASHI_P1_SPOOL"
spool="$(cd "$DASHI_P1_SPOOL" && pwd -P)"

# Source/alpha/negative-control tests are not Lean proof receipts.
python3 -m unittest discover -s "$p1495/tests" \
  -p 'test_lean_world_native_v3_projection.py' -v
python3 -m unittest discover -s "$p1495/tests" \
  -p 'test_lean_world_native_p1_codec.py' -v
export DASHI_LEAN_P1_CODEC="$p1_codec"
python3 -m unittest discover -s "$root/tests" \
  -p 'test_lean_world_native_p1_pg.py' -v

observation="$(
  python3 "$p1495/scripts/run_lean_world_native_v3_projection.py" \
    --manifest "$DASHI_HANDOFF_MANIFEST" \
    --declaration "$DASHI_HANDOFF_DECLARATION" \
    --spool "$spool" |
    python3 -c 'import json,sys;print(json.load(sys.stdin)["path"])'
)"
test -f "$observation"
jmd_args=()
if [ -n "${DASHI_PR105_WORKTREE:-}" ]; then
  jmd_owner="$(cd "$DASHI_PR105_WORKTREE" && pwd -P)/scripts/build_jmd_lean_ast_world.py"
  test -f "$jmd_owner"
  native_export="$(python3 - "$DASHI_HANDOFF_MANIFEST" <<'PY'
import json,sys
manifest=json.load(open(sys.argv[1],encoding="utf-8"))
print(manifest["artifact_path"])
PY
)"
  test -f "$native_export"
  jmd_args=(--jmd-builder-source "$jmd_owner" --native-export "$native_export")
fi
p1_receipt="$(
  python3 "$root/scripts/run_lean_world_native_p1_pg.py" \
    --schema "$DASHI_WORLD_SCHEMA" \
    --observation "$observation" \
    --p1-codec "$p1_codec" \
    --acknowledge-candidate-only "${jmd_args[@]}"
)"
printf '%s\n' "$p1_receipt"

# These two consumers use exactly the SAME source-bound type/proof bytes:
# typed fibre lookup and compressed Expr baseline. They do not certify Lean.
python3 - "$p1_receipt" "$root" "$DASHI_WORLD_SCHEMA" <<'PYCODE'
import json
import subprocess
import sys
row=json.loads(sys.argv[1])
script=sys.argv[2]+"/scripts/run_lean_world_p1_common_consumers.py"
subprocess.run([
    sys.executable,script,
    "--schema",sys.argv[3],
    "--repository",row["repository"],
    "--revision",row["revision"],
    "--path",row["source_path"],
    "--declaration",row["declaration"],
    "--export-sha256",row["export_sha256"],
    "--top-k","25",
],check=True)
PYCODE

echo "P1_SOURCE_BOUND_OBSERVATION_STORED (no proof/world admission)"
echo "Original immutable native observation: $observation"
