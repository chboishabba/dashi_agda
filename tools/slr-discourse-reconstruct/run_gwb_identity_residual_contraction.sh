#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
WORLD="$OUT_DIR/sensiblaw-gwb-candidate-world-model-wikimedia-followed.json"
SEEDS="$OUT_DIR/gwb-wikimedia-seeds.jsonl"
GRAPH="$OUT_DIR/gwb-wikimedia-world-graph.json"
OUTPUT_WORLD="$OUT_DIR/sensiblaw-gwb-candidate-world-model-wikimedia-identity-contracted.json"
SIDECAR="$OUT_DIR/gwb-wikimedia-identity-contractions.json"
ERR="$OUT_DIR/gwb-wikimedia-identity-contraction.stderr"

for required in "$WORLD" "$SEEDS" "$GRAPH"; do
  [[ -s "$required" ]] || { echo "ERROR: missing required input $required" >&2; exit 1; }
done

python3 "$HERE/slr_gwb_identity_residual_contraction.py" \
  --world-model "$WORLD" \
  --seeds "$SEEDS" \
  --graph "$GRAPH" \
  --output-model "$OUTPUT_WORLD" \
  --output-sidecar "$SIDECAR" \
  2> "$ERR"

grep -q 'schema=slr-gwb-wikimedia-identity-contraction-v1' "$ERR" || {
  echo 'ERROR: GWB Wikimedia identity contraction receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'topic_anchor_is_source_object_identity=false' "$ERR" || {
  echo 'ERROR: topic anchor collapsed into source-work identity' >&2
  exit 1
}
grep -q 'wikimedia_identity_creates_claim_truth=false' "$ERR" || {
  echo 'ERROR: Wikidata identity was promoted to claim truth' >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$ERR" || {
  echo 'ERROR: identity contraction attempted semantic promotion' >&2
  exit 1
}

python3 - "$SIDECAR" "$OUTPUT_WORLD" <<'PY'
import json, sys
sidecar = json.load(open(sys.argv[1], encoding='utf-8'))
world = json.load(open(sys.argv[2], encoding='utf-8'))
s = sidecar['summary']
assert s['documents'] == 10
assert s['source_work_identity_paid'] == 2
assert s['source_work_identity_unpaid'] == 8
assert s['topic_anchor_paid'] == 8
assert s['runtime_resolved_work_identities'] == 1
by_doc = {int(x['document_ordinal']): x for x in sidecar['contractions']}
assert by_doc[8]['source_work_identity_status'] == 'paid'
assert by_doc[8]['source_work_qid'] == 'Q16156115'
assert by_doc[10]['source_work_identity_status'] == 'paid'
assert by_doc[10]['source_work_qid'] == 'Q942966'
for ordinal in (1,2,3,4,5,6,7,9):
    assert by_doc[ordinal]['source_work_identity_status'] == 'unpaid'
assert sidecar['topic_anchor_is_source_object_identity'] is False
assert sidecar['wikimedia_identity_creates_claim_truth'] is False
assert world['metadata']['semantic_promotion'] is False
print(
    'SLR_GWB_WIKIMEDIA_IDENTITY_CONTRACTION_VALIDATION '
    'documents=10 source_work_identity_paid=2 source_work_identity_unpaid=8 '
    'topic_anchor_paid=8 runtime_resolved_work_identities=1 '
    'family_of_secrets_qid=Q16156115 decision_points_qid=Q942966 '
    'claim_truth_promoted=false candidate_only=true semantic_promotion=false'
)
PY

cat "$ERR"
printf 'contracted_world=%s\nidentity_sidecar=%s\n' "$OUTPUT_WORLD" "$SIDECAR"
