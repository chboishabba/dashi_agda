#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
UNLABELLED="${1:-$HERE/specimens/9-sept-8-03pm-unlabelled}"
LABELLED="${2:-$HERE/specimens/abc730-2026-09-09-primary}"

bash "$HERE/run_fragment_evidence_contraction.sh" "$UNLABELLED" "$LABELLED" >/dev/null

CONTRACTED="$UNLABELLED/sensiblaw-candidate-world-model-fragment-evidence-contracted.json"
MANIFEST="$LABELLED/source.json"
GATES="$UNLABELLED/c029-consumer-gates-derived.json"
CONSTRAINED="$UNLABELLED/sensiblaw-candidate-world-model-fragment-evidence-constrained.json"
FIBRES="$UNLABELLED/fragment-evidence-world-constraint-fibres.json"
FIBRE_ERR="$UNLABELLED/fragment-evidence-world-constraint-fibres.stderr"
REVIEW="$UNLABELLED/fragment-evidence-review-dispositions.json"
REVIEW_ERR="$UNLABELLED/fragment-evidence-review-dispositions.stderr"

[[ -s "$CONTRACTED" ]] || { echo "ERROR: missing contracted world $CONTRACTED" >&2; exit 1; }
[[ -s "$MANIFEST" ]] || { echo "ERROR: missing manifest $MANIFEST" >&2; exit 1; }
[[ -s "$GATES" ]] || { echo "ERROR: missing derived gates $GATES" >&2; exit 1; }

BASE_SHA_BEFORE="$(sha256sum "$CONTRACTED" | awk '{print $1}')"
python3 "$HERE/slr_world_constraint_fibre.py" \
  --world-model "$CONTRACTED" \
  --source-manifest "$MANIFEST" \
  --output-model "$CONSTRAINED" \
  --output-fibres "$FIBRES" \
  2> "$FIBRE_ERR"
BASE_SHA_AFTER="$(sha256sum "$CONTRACTED" | awk '{print $1}')"
[[ "$BASE_SHA_BEFORE" == "$BASE_SHA_AFTER" ]] || {
  echo "ERROR: contracted candidate world was rewritten by world-constraint attachment" >&2
  exit 1
}

grep -q 'schema=slr-world-constraint-fibre-v1' "$FIBRE_ERR" || {
  echo 'ERROR: world constraint receipt missing/stale' >&2
  cat "$FIBRE_ERR" >&2
  exit 1
}
grep -q 'append_only=true' "$FIBRE_ERR" || { echo 'ERROR: world constraint append-only firewall missing' >&2; exit 1; }
grep -q 'semantic_promotion=false' "$FIBRE_ERR" || { echo 'ERROR: world constraint semantic-promotion firewall missing' >&2; exit 1; }

bash "$HERE/run_review_disposition.sh" \
  "$UNLABELLED" \
  "$GATES" \
  "$CONSTRAINED" \
  "$FIBRES" \
  "$REVIEW" \
  "$REVIEW_ERR" >/dev/null

python3 - "$UNLABELLED/fragment-evidence-contractions.json" "$GATES" "$REVIEW" <<'PY'
import json, sys
sidecar = json.load(open(sys.argv[1], encoding='utf-8'))
gates = json.load(open(sys.argv[2], encoding='utf-8'))
review = json.load(open(sys.argv[3], encoding='utf-8'))
assert sidecar['schema'] == 'slr-fragment-evidence-contraction-v2'
assert sidecar['append_only'] is True
assert sidecar['historical_residuals_rewritten'] is False
assert sidecar['claim_truth_promoted'] is False
assert gates['current_residual'] == sidecar['summary']['c029_current_first_residual']
assert gates['evaluate_aptness_enabled'] is sidecar['summary']['c029_consumer_adequate']
assert review['current_residual'] == gates['current_residual']
assert review['promotion_performed'] is False
assert review['semantic_promotion'] is False
print(
    'SLR_FRAGMENT_EVIDENCE_REVIEW_LOOP_VALIDATION '
    f"paid_obligations={sidecar['summary']['paid_obligation_count']} "
    f"partial_or_nonpaying={sidecar['summary']['partial_or_nonpaying_receipt_count']} "
    f"c029_adequate={str(sidecar['summary']['c029_consumer_adequate']).lower()} "
    f"current_residual={sidecar['summary']['c029_current_first_residual']} "
    f"reject={review['summary'].get('reject-by-consumer-veto',0)} "
    f"abstain={review['summary'].get('abstain-for-residual',0)} "
    f"eligible={review['summary'].get('eligible-for-separate-promotion-review',0)} "
    'promotion_performed=false semantic_promotion=false append_only=true'
)
PY

cat "$UNLABELLED/fragment-evidence-contractions.stderr"
cat "$FIBRE_ERR"
cat "$REVIEW_ERR"
printf 'contracted_world=%s\nconstrained_world=%s\nfibres=%s\nderived_gates=%s\nreview=%s\n' \
  "$CONTRACTED" "$CONSTRAINED" "$FIBRES" "$GATES" "$REVIEW"
