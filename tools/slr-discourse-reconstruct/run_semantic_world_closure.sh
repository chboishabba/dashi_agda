#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
OUT_DIR="${1:-/tmp/slr-validation-20260911/gwb-world}"
LANGUAGES="${2:-en,es,fr,de,simple}"
GRAPH="$OUT_DIR/gwb-wikimedia-world-graph.json"
MULTI="$OUT_DIR/gwb-multilingual-wikimedia-parser-compat.json"
CACHE="$OUT_DIR/semantic-world-http-cache"
OUTPUT="$OUT_DIR/gwb-semantic-world-closure.json"
ERR="$OUT_DIR/gwb-semantic-world-closure.stderr"

python3 "$HERE/slr_semantic_world_closure.py" --self-check 2> "$OUT_DIR/gwb-semantic-world-closure-self-check.stderr"

grep -q 'passed=true' "$OUT_DIR/gwb-semantic-world-closure-self-check.stderr" || {
  echo 'ERROR: semantic closure self-check failed' >&2
  cat "$OUT_DIR/gwb-semantic-world-closure-self-check.stderr" >&2
  exit 1
}

args=(
  --graph "$GRAPH"
  --cache-dir "$CACHE"
  --output "$OUTPUT"
  --languages "$LANGUAGES"
)
if [[ -s "$MULTI" ]]; then
  args+=(--multilingual-compat "$MULTI")
fi
python3 "$HERE/slr_semantic_world_closure.py" "${args[@]}" 2> "$ERR"

grep -q 'schema=slr-semantic-world-closure-v1' "$ERR" || {
  echo 'ERROR: semantic closure receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'target_surface_asserted=false' "$ERR" || {
  echo 'ERROR: propagated semantic evidence rewrote target surface assertion' >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$ERR" || {
  echo 'ERROR: semantic closure attempted promotion' >&2
  exit 1
}
cat "$ERR"
printf 'semantic_world_closure=%s\nsemantic_world_cache=%s\n' "$OUTPUT" "$CACHE"
