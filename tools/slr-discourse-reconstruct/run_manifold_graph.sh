#!/usr/bin/env bash
set -euo pipefail

SPECIMEN="${1:-/tmp/slr-specimens/9-sept-8-03pm}"
CUTS="${SPECIMEN}/discourse-cuts-transcript-wide.tsv"
PARSER="${SPECIMEN}/parser.tsv"
SOURCE="${SPECIMEN}/source.txt"
PNF="${SPECIMEN}/pnf.stdout"
MANIFOLD="${SPECIMEN}/discourse-manifold-transcript-wide.tsv"
GRAPH="${SPECIMEN}/discourse-graph-transcript-wide.tsv"

cargo run --release --bin slr-discourse-manifold -- \
  --cuts "$CUTS" \
  --parser "$PARSER" \
  --source "$SOURCE" \
  --pnf "$PNF" \
  --max-rank 3 \
  --top 5000 \
  > "$MANIFOLD" \
  2> "${SPECIMEN}/discourse-manifold-transcript-wide.stderr"

cargo run --release --bin slr-discourse-graph -- \
  --manifold "$MANIFOLD" \
  > "$GRAPH" \
  2> "${SPECIMEN}/discourse-graph-transcript-wide.stderr"

printf 'manifold=%s\ngraph=%s\n' "$MANIFOLD" "$GRAPH"
