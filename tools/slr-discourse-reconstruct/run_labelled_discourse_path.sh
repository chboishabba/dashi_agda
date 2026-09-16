#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
UNLABELLED="${1:-$HERE/specimens/9-sept-8-03pm-unlabelled}"
LABELLED="${2:-$HERE/specimens/abc730-2026-09-09-primary}"
SLR_ROOT="${3:-/home/c/Documents/code/slr}"
PROFILES="${4:-speaker-profiles.example.tsv}"

[[ -s "$UNLABELLED/source.txt" ]] || { echo "ERROR: missing noisy source $UNLABELLED/source.txt" >&2; exit 1; }
[[ -s "$LABELLED/source.txt" ]] || { echo "ERROR: missing labelled source $LABELLED/source.txt" >&2; exit 1; }

if [[ ! -s "$UNLABELLED/abc730-gold-boundaries.tsv" ]]; then
  bash "$HERE/run_abc730_gold_benchmark.sh" "$UNLABELLED" "$LABELLED" "$SLR_ROOT" "$PROFILES" >/dev/null
fi

CUTS="$HERE/../../fixtures/slr/abc730-west-bank-sanctions-2026-09-09-intrasentence-cuts.jsonl"
OUT_JSON="$UNLABELLED/abc730-labelled-discourse-path.json"
OUT_TSV="$UNLABELLED/abc730-labelled-discourse-path.tsv"
ERR="$UNLABELLED/abc730-labelled-discourse-path.stderr"

python3 "$HERE/slr_labelled_discourse_path.py" \
  --source "$UNLABELLED/source.txt" \
  --parser "$UNLABELLED/parser.tsv" \
  --gold-boundaries "$UNLABELLED/abc730-gold-boundaries.tsv" \
  --cuts "$CUTS" \
  --output-json "$OUT_JSON" \
  --output-tsv "$OUT_TSV" \
  2> "$ERR"

grep -q 'schema=slr-labelled-discourse-path-v1' "$ERR" || { echo 'ERROR: labelled discourse path receipt missing/stale' >&2; cat "$ERR" >&2; exit 1; }
grep -q 'skip_intermediate_speaker_forbidden=true' "$ERR" || { echo 'ERROR: skip-edge firewall missing' >&2; exit 1; }
grep -q 'semantic_promotion=false' "$ERR" || { echo 'ERROR: semantic promotion firewall missing' >&2; exit 1; }

python3 - "$OUT_JSON" <<'PY'
import json, sys
m=json.load(open(sys.argv[1], encoding='utf-8'))
assert m['schema']=='slr-labelled-discourse-path-v1'
assert m['skip_intermediate_speaker_forbidden'] is True
assert m['candidate_only'] is True
assert m['semantic_promotion'] is False
assert m['claim_truth_promoted'] is False
for p in m['paths']:
    if p['intermediate_speakers']:
        assert p['skip_edge_permitted'] is False
print(
    'SLR_LABELLED_DISCOURSE_PATH_VALIDATION '
    f"paths={m['summary']['paths']} direct={m['summary']['direct_paths']} "
    f"multihop={m['summary']['multihop_paths']} exact_hops={m['summary']['exact_hops']} "
    f"bounded_hops={m['summary']['bounded_hops']} unpaid_hops={m['summary']['unpaid_hops']} "
    'candidate_only=true semantic_promotion=false'
)
PY

cat "$ERR"
printf 'path_json=%s\npath_tsv=%s\n' "$OUT_JSON" "$OUT_TSV"
