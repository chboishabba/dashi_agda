#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
UNLABELLED="${1:-$HERE/specimens/9-sept-8-03pm-unlabelled}"
LABELLED="${2:-$HERE/specimens/abc730-2026-09-09-primary}"
SLR_ROOT="${3:-/home/c/Documents/code/slr}"
PROFILES="${4:-speaker-profiles.example.tsv}"

[[ -s "$UNLABELLED/source.txt" ]] || { echo "ERROR: missing noisy source $UNLABELLED/source.txt" >&2; exit 1; }
[[ -s "$LABELLED/source.txt" ]] || { echo "ERROR: missing labelled source $LABELLED/source.txt" >&2; exit 1; }

if [[ ! -s "$UNLABELLED/parser.tsv" ]]; then
  "$SLR_ROOT/.venv/bin/python" "$SLR_ROOT/python/spacy_stream.py" \
    --model en_core_web_sm "$UNLABELLED/source.txt" \
    > "$UNLABELLED/parser.tsv" \
    2> "$UNLABELLED/spacy.stderr"
fi

if [[ ! -s "$UNLABELLED/pnf.stdout" ]]; then
  "$SLR_ROOT/target/release/sensiblaw-stream" \
    < "$UNLABELLED/parser.tsv" \
    > "$UNLABELLED/pnf.stdout" \
    2> "$UNLABELLED/pnf.stderr"
fi

if [[ ! -s "$UNLABELLED/discourse-quality-transcript-wide.tsv" ]]; then
  args=("$UNLABELLED")
  [[ -n "$PROFILES" ]] && args+=("$PROFILES")
  bash "$HERE/run_transcript_wide.sh" "${args[@]}"
  bash "$HERE/run_transcript_fibres.sh" "$UNLABELLED"
  bash "$HERE/run_manifold_graph.sh" "$UNLABELLED"
  bash "$HERE/run_span_reconstruction.sh" "$UNLABELLED"
  bash "$HERE/run_discourse_quality.sh" "$UNLABELLED"
fi

OUT_JSON="$UNLABELLED/abc730-gold-benchmark.json"
OUT_TSV="$UNLABELLED/abc730-gold-boundaries.tsv"
ERR="$UNLABELLED/abc730-gold-benchmark.stderr"

python3 "$HERE/slr_abc_gold_benchmark.py" \
  --unlabelled-source "$UNLABELLED/source.txt" \
  --labelled-source "$LABELLED/source.txt" \
  --parser "$UNLABELLED/parser.tsv" \
  --quality "$UNLABELLED/discourse-quality-transcript-wide.tsv" \
  --span-stderr "$UNLABELLED/discourse-spans-transcript-wide.stderr" \
  --output-json "$OUT_JSON" \
  --output-tsv "$OUT_TSV" \
  2> "$ERR"

grep -q 'schema=slr-abc-gold-benchmark-v1' "$ERR" || {
  echo 'ERROR: gold benchmark receipt missing or stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'label_scope=explicit-speaker-turns-only' "$ERR" || {
  echo 'ERROR: gold benchmark label scope missing' >&2
  exit 1
}
grep -q 'quote_nesting_scored=false' "$ERR" || {
  echo 'ERROR: quote/nesting no-promotion boundary missing' >&2
  exit 1
}
grep -q 'benchmark_promotes_truth=false' "$ERR" || {
  echo 'ERROR: benchmark truth-promotion firewall missing' >&2
  exit 1
}

python3 - "$OUT_JSON" <<'PY'
import json
import sys
from pathlib import Path

report = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
assert report["schema"] == "slr-abc-gold-benchmark-v1"
assert report["label_scope"] == "explicit-speaker-turns-only"
assert report["semantic_promotion"] is False
assert report["benchmark_promotes_truth"] is False
assert report["quote_nesting_accuracy"]["status"] == "not-scored"
assert report["uncertainty_calibration"]["status"] == "coverage-only-not-probability-calibrated"
print(
    "SLR_ABC_GOLD_BENCHMARK_VALIDATION "
    f"hidden_gold={report['gold']['hidden_within_parser_sentence']} "
    f"precision_milli={report['speaker_boundary']['precision_milli']} "
    f"recall_milli={report['speaker_boundary']['recall_milli']} "
    f"hidden_recovery_milli={report['hidden_splice']['recovery_milli']} "
    "semantic_promotion=false"
)
PY

cat "$ERR"
printf 'benchmark_json=%s\ngold_boundaries=%s\n' "$OUT_JSON" "$OUT_TSV"
