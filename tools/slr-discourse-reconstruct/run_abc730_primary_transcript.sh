#!/usr/bin/env bash
set -euo pipefail

SLR_ROOT="${1:-/home/c/Documents/code/slr}"
PROFILES="${2:-speaker-profiles.example.tsv}"
SENSIBLAW_ROOT="${SENSIBLAW_ROOT:-/home/c/Documents/code/SensibLaw}"
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
bash "$HERE/run_transcript_fibres.sh" "$SPECIMEN"
bash "$HERE/run_manifold_graph.sh" "$SPECIMEN"
bash "$HERE/run_span_reconstruction.sh" "$SPECIMEN"
bash "$HERE/run_discourse_quality.sh" "$SPECIMEN"
bash "$HERE/run_sensiblaw_world_adapter.sh" "$SPECIMEN"
bash "$HERE/run_claim_projection.sh" "$SPECIMEN"
bash "$HERE/run_world_constraint_fibre.sh" "$SPECIMEN"
bash "$HERE/run_review_disposition.sh" "$SPECIMEN" "$SPECIMEN/c029-consumer-gates.json"

PARITY_STATUS="not-run"
if [[ -d "$SENSIBLAW_ROOT/src" ]]; then
  bash "$HERE/run_sensiblaw_world_parity.sh" "$SPECIMEN" "$SENSIBLAW_ROOT" >/dev/null
  PARITY_STATUS="passed"
fi

printf '\nABC730_PRIMARY_PIPELINE_RECEIPT specimen=%s source_role=speaker-labelled-primary programme_same_object=true sensiblaw_world_adapter=true canonical_claim_projection=candidate-only world_constraint_fibre=attached-candidate-only review_consumer=c029-abstain-or-veto sensiblaw_normalization_parity=%s semantic_promotion=false\n' "$SPECIMEN" "$PARITY_STATUS"
printf 'Run outputs:\n  %s\n  %s\n  %s\n  %s\n  %s\n  %s\n  %s\n  %s\n  %s\n' \
  "$SPECIMEN/discourse-graph-transcript-wide.tsv" \
  "$SPECIMEN/discourse-spans-transcript-wide.tsv" \
  "$SPECIMEN/discourse-quality-transcript-wide.tsv" \
  "$SPECIMEN/sensiblaw-candidate-world-model.json" \
  "$SPECIMEN/sensiblaw-candidate-world-model-with-claims.json" \
  "$SPECIMEN/world-constraint-fibres.json" \
  "$SPECIMEN/sensiblaw-candidate-world-model-constrained.json" \
  "$SPECIMEN/review-dispositions.json" \
  "$SPECIMEN/source-reconstructed.txt"
