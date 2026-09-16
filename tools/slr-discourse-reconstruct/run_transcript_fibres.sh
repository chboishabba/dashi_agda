#!/usr/bin/env bash
set -euo pipefail

SPECIMEN_DIR="${1:?usage: run_transcript_fibres.sh SPECIMEN_DIR [CUTS_TSV]}"
CUTS="${2:-$SPECIMEN_DIR/discourse-cuts-transcript-wide.tsv}"
PARSER="$SPECIMEN_DIR/parser.tsv"
SOURCE="$SPECIMEN_DIR/source.txt"
OUT="$SPECIMEN_DIR/discourse-fibres-transcript-wide.tsv"
ERR="$SPECIMEN_DIR/discourse-fibres-transcript-wide.stderr"

cargo run --release --bin slr-discourse-fibres -- \
  --cuts "$CUTS" \
  --parser "$PARSER" \
  --source "$SOURCE" \
  --max-rank 3 \
  --top 600 \
  > "$OUT" 2> "$ERR"

printf 'wrote %s\n' "$OUT"
printf 'wrote %s\n' "$ERR"
