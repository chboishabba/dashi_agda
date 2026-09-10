#!/usr/bin/env bash
set -euo pipefail
SPECIMEN="${1:-/tmp/slr-specimens/9-sept-8-03pm}"
OUT="${SPECIMEN}/subject-transitions-transcript-wide.tsv"
ERR="${SPECIMEN}/subject-transitions-transcript-wide.stderr"
cargo run --release --bin slr-subject-transition -- \
  --parser "${SPECIMEN}/parser.tsv" \
  --graph "${SPECIMEN}/discourse-graph-transcript-wide.tsv" \
  > "$OUT" 2> "$ERR"
printf 'subject_transitions=%s\nstderr=%s\n' "$OUT" "$ERR"
