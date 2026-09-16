#!/usr/bin/env bash
set -euo pipefail

SPECIMEN="${1:-/tmp/slr-specimens/9-sept-8-03pm}"
GRAPH="${SPECIMEN}/discourse-graph-transcript-wide.tsv"
ROLES="${SPECIMEN}/role-transitions-transcript-wide.tsv"
OUT="${SPECIMEN}/discourse-quality-transcript-wide.tsv"
ERR="${SPECIMEN}/discourse-quality-transcript-wide.stderr"

[[ -s "$GRAPH" ]] || { echo "ERROR: missing graph $GRAPH" >&2; exit 1; }
[[ -s "$ROLES" ]] || bash "$(dirname "$0")/run_role_transitions.sh" "$SPECIMEN" >/dev/null

cargo run --release --bin slr-discourse-quality -- \
  --graph "$GRAPH" \
  --roles "$ROLES" \
  > "$OUT" 2> "$ERR"

grep -q 'schema=slr-discourse-quality-v1' "$ERR" || {
  echo 'ERROR: discourse-quality receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}

printf 'quality=%s\nstderr=%s\n' "$OUT" "$ERR"
