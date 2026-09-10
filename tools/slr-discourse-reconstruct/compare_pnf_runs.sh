#!/usr/bin/env bash
set -euo pipefail

RAW="${1:-/tmp/slr-specimens/9-sept-8-03pm/pnf.stdout}"
RECON="${2:-/tmp/slr-specimens/9-sept-8-03pm-reconstructed/pnf.stdout}"
OUT="${3:-/tmp/slr-specimens/9-sept-8-03pm/pnf-raw-vs-reconstructed.tsv}"
ERR="${OUT%.tsv}.stderr"

cargo run --release --bin slr-pnf-compare -- \
  --raw-pnf "$RAW" \
  --reconstructed-pnf "$RECON" \
  > "$OUT" \
  2> "$ERR"

printf 'comparison=%s\nreceipt=%s\n' "$OUT" "$ERR"
