#!/usr/bin/env bash
set -euo pipefail

SPECIMEN="${1:-/tmp/slr-specimens/9-sept-8-03pm}"
GRAPH="${SPECIMEN}/discourse-graph-transcript-wide.tsv"
PARSER="${SPECIMEN}/parser.tsv"
SOURCE="${SPECIMEN}/source.txt"
LEDGER="${SPECIMEN}/discourse-spans-transcript-wide.tsv"
RECON="${SPECIMEN}/source-reconstructed.txt"

cargo run --release --bin slr-discourse-spans -- \
  --graph "$GRAPH" \
  --parser "$PARSER" \
  --source "$SOURCE" \
  --ledger "$LEDGER" \
  --reconstructed "$RECON" \
  2> "${SPECIMEN}/discourse-spans-transcript-wide.stderr"

printf 'ledger=%s\nreconstructed=%s\n' "$LEDGER" "$RECON"
printf '\nNext: rerun the existing spaCy -> SLR/PNF pipeline on %s into a separate reconstructed specimen directory.\n' "$RECON"
