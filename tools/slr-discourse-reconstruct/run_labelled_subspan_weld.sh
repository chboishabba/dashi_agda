#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
UNLABELLED="${1:-$HERE/specimens/9-sept-8-03pm-unlabelled}"
LABELLED="${2:-$HERE/specimens/abc730-2026-09-09-primary}"
SLR_ROOT="${3:-/home/c/Documents/code/slr}"
PROFILES="${4:-speaker-profiles.example.tsv}"
GOLD_TSV="$UNLABELLED/abc730-gold-boundaries.tsv"
OUT_JSON="$UNLABELLED/abc730-labelled-subspan-weld.json"
OUT_TSV="$UNLABELLED/abc730-labelled-subspan-weld.tsv"
ERR="$UNLABELLED/abc730-labelled-subspan-weld.stderr"
CUTS="$HERE/../../fixtures/slr/abc730-west-bank-sanctions-2026-09-09-intrasentence-cuts.jsonl"

[[ -s "$UNLABELLED/source.txt" ]] || { echo "ERROR: missing noisy source $UNLABELLED/source.txt" >&2; exit 1; }
[[ -s "$UNLABELLED/parser.tsv" ]] || { echo "ERROR: missing noisy parser $UNLABELLED/parser.tsv" >&2; exit 1; }
[[ -s "$LABELLED/source.txt" ]] || { echo "ERROR: missing labelled source $LABELLED/source.txt" >&2; exit 1; }
[[ -s "$CUTS" ]] || { echo "ERROR: missing cut fixture $CUTS" >&2; exit 1; }

if [[ ! -s "$GOLD_TSV" ]]; then
  bash "$HERE/run_abc730_gold_benchmark.sh" "$UNLABELLED" "$LABELLED" "$SLR_ROOT" "$PROFILES" >/dev/null
fi

python3 "$HERE/slr_labelled_subspan_weld.py" \
  --source "$UNLABELLED/source.txt" \
  --parser "$UNLABELLED/parser.tsv" \
  --gold-boundaries "$GOLD_TSV" \
  --cuts "$CUTS" \
  --output-json "$OUT_JSON" \
  --output-tsv "$OUT_TSV" \
  2> "$ERR"

grep -q 'schema=slr-labelled-subspan-weld-v1' "$ERR" || {
  echo 'ERROR: labelled subspan weld receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'exact_requires_exact_neighbour=true' "$ERR" || {
  echo 'ERROR: exact-weld confidence firewall missing' >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$ERR" || {
  echo 'ERROR: subspan weld attempted semantic promotion' >&2
  exit 1
}

python3 - "$OUT_JSON" <<'PY'
import json, sys
m = json.load(open(sys.argv[1], encoding='utf-8'))
assert m['schema'] == 'slr-labelled-subspan-weld-v1'
assert m['candidate_only'] is True
assert m['semantic_promotion'] is False
assert m['claim_truth_promoted'] is False
assert all(row['weld_state'] in {'exact','bounded','unpaid'} for row in m['welds'])
assert all((row['weld_state'] != 'exact') or row['alignment_confidence'] == 'exact-neighbour' for row in m['welds'])
print(
    'SLR_LABELLED_SUBSPAN_WELD_VALIDATION '
    f"cuts={m['summary']['cuts']} exact={m['summary']['exact']} "
    f"bounded={m['summary']['bounded']} unpaid={m['summary']['unpaid']} "
    'candidate_only=true semantic_promotion=false'
)
PY

cat "$ERR"
printf 'weld_json=%s\nweld_tsv=%s\nstderr=%s\n' "$OUT_JSON" "$OUT_TSV" "$ERR"
