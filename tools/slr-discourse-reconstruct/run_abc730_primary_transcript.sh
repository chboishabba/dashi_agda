#!/usr/bin/env bash
set -euo pipefail

SLR_ROOT="${1:-/home/c/Documents/code/slr}"
PROFILES="${2:-speaker-profiles.example.tsv}"
HERE="$(cd "$(dirname "$0")" && pwd)"
SPECIMEN="$HERE/specimens/abc730-2026-09-09-primary"

bash "$HERE/fetch_abc730_primary_transcript.sh" \
  "https://www.abc.net.au/news/2026-09-09/new-sanctions-placed-on-israeli-settlements-/107135268" \
  "$SPECIMEN"

"$SLR_ROOT/.venv/bin/python" "$SLR_ROOT/python/spacy_stream.py" \
  --model en_core_web_sm "$SPECIMEN/source.txt" \
  > "$SPECIMEN/parser.tsv" \
  2> "$SPECIMEN/spacy.stderr"

"$SLR_ROOT/target/release/sensiblaw-stream" \
  < "$SPECIMEN/parser.tsv" \
  > "$SPECIMEN/pnf.stdout" \
  2> "$SPECIMEN/pnf.stderr"

args=("$SPECIMEN")
[[ -n "$PROFILES" ]] && args+=("$PROFILES")
bash "$HERE/run_transcript_wide.sh" "${args[@]}"
bash "$HERE/run_transcript_fibres.sh" "${args[@]}"
bash "$HERE/run_manifold_graph.sh" "$SPECIMEN"
bash "$HERE/run_span_reconstruction.sh" "$SPECIMEN"
bash "$HERE/run_discourse_quality.sh" "$SPECIMEN"

printf '\nABC730_PRIMARY_PIPELINE_RECEIPT specimen=%s source_role=speaker-labelled-primary programme_same_object=true semantic_promotion=false\n' "$SPECIMEN"
printf 'Run outputs:\n  %s\n  %s\n  %s\n  %s\n' \
  "$SPECIMEN/discourse-graph-transcript-wide.tsv" \
  "$SPECIMEN/discourse-spans-transcript-wide.tsv" \
  "$SPECIMEN/discourse-quality-transcript-wide.tsv" \
  "$SPECIMEN/source-reconstructed.txt"
