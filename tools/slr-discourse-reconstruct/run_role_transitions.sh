#!/usr/bin/env bash
set -euo pipefail
SPECIMEN="${1:-/tmp/slr-specimens/9-sept-8-03pm}"
PARSER="${SPECIMEN}/parser.tsv"
GRAPH="${SPECIMEN}/discourse-graph-transcript-wide.tsv"
OUT="${SPECIMEN}/role-transitions-transcript-wide.tsv"
ERR="${SPECIMEN}/role-transitions-transcript-wide.stderr"

cargo run --release --bin slr-role-transition -- \
  --parser "$PARSER" \
  --graph "$GRAPH" \
  > "$OUT" 2> "$ERR"

grep -q 'schema=slr-role-transition-v1' "$ERR" || {
  echo 'ERROR: role transition receipt missing' >&2
  cat "$ERR" >&2
  exit 1
}
printf 'roles=%s\nstderr=%s\n' "$OUT" "$ERR"
