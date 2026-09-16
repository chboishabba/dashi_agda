#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
UNLABELLED="${1:-$HERE/specimens/9-sept-8-03pm-unlabelled}"
LABELLED="${2:-$HERE/specimens/abc730-2026-09-09-primary}"
WORLD="${UNLABELLED}/sensiblaw-candidate-world-model-with-fragment-residuals.json"
EVIDENCE_MANIFEST="${LABELLED}/source.json"
RESIDUAL_MAP="${LABELLED}/canonical-claim-residuals.json"
PAYMENTS="${LABELLED}/c029-evidence-payment-receipts.json"
OUT_MODEL="${UNLABELLED}/sensiblaw-candidate-world-model-fragment-evidence-contracted.json"
OUT_SIDECAR="${UNLABELLED}/fragment-evidence-contractions.json"
OUT_GATES="${UNLABELLED}/c029-consumer-gates-derived.json"
OUT_REPORT="${UNLABELLED}/fragment-evidence-contraction-report.json"
ERR="${UNLABELLED}/fragment-evidence-contractions.stderr"

if [[ ! -s "$WORLD" ]]; then
  bash "$HERE/run_claim_fragment_residual_inheritance.sh" "$UNLABELLED" "$RESIDUAL_MAP" >/dev/null
fi
[[ -s "$WORLD" ]] || { echo "ERROR: missing fragment residual world $WORLD" >&2; exit 1; }
[[ -s "$EVIDENCE_MANIFEST" ]] || { echo "ERROR: missing labelled evidence manifest $EVIDENCE_MANIFEST" >&2; exit 1; }
[[ -s "$RESIDUAL_MAP" ]] || { echo "ERROR: missing residual map $RESIDUAL_MAP" >&2; exit 1; }
[[ -s "$PAYMENTS" ]] || { echo "ERROR: missing payment receipts $PAYMENTS" >&2; exit 1; }

python3 "$HERE/slr_fragment_evidence_contraction.py" \
  --world "$WORLD" \
  --evidence-manifest "$EVIDENCE_MANIFEST" \
  --residual-map "$RESIDUAL_MAP" \
  --payments "$PAYMENTS" \
  --output-model "$OUT_MODEL" \
  --output-sidecar "$OUT_SIDECAR" \
  --output-gates "$OUT_GATES" \
  --output-report "$OUT_REPORT" \
  2> "$ERR"

grep -q 'schema=slr-fragment-evidence-contraction-v2' "$ERR" || {
  echo 'ERROR: fragment evidence contraction receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'fragment_provenance_is_evidence_authority=false' "$ERR" || {
  echo 'ERROR: fragment provenance conflated with evidence authority' >&2
  exit 1
}
grep -q 'historical_residuals_rewritten=false' "$ERR" || {
  echo 'ERROR: historical residual rows were treated as mutable state' >&2
  exit 1
}
grep -q 'whole_claim_extent_paid=false' "$ERR" || {
  echo 'ERROR: evidence contraction promoted local fragment to whole claim extent' >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$ERR" || {
  echo 'ERROR: semantic promotion attempted' >&2
  exit 1
}

python3 - "$OUT_MODEL" "$OUT_SIDECAR" "$OUT_GATES" "$OUT_REPORT" <<'PY'
import json, sys
m = json.load(open(sys.argv[1], encoding='utf-8'))
s = json.load(open(sys.argv[2], encoding='utf-8'))
g = json.load(open(sys.argv[3], encoding='utf-8'))
r = json.load(open(sys.argv[4], encoding='utf-8'))
assert m['schema_version'] == 'sl.candidate_world_model.v0_1'
meta = m['metadata']['fragment_evidence_contraction']
assert meta['schema'] == 'slr-fragment-evidence-contraction-v2'
assert meta['fragment_provenance_is_evidence_authority'] is False
assert meta['evidence_authority_rewrites_fragment_provenance'] is False
assert meta['historical_residuals_rewritten'] is False
assert meta['whole_claim_extent_paid'] is False
assert meta['claim_truth_promoted'] is False
assert meta['candidate_only'] is True
assert meta['semantic_promotion'] is False
assert s['append_only'] is True
assert s['semantic_promotion'] is False
assert s['historical_residuals_rewritten'] is False
assert s['claim_truth_promoted'] is False
assert g['schema'] == 'c029-consumer-gates-v1'
assert g['candidate_only'] is True
assert g['semantic_promotion'] is False
assert g['truth_promoted'] is False
assert g['current_residual'] == s['summary']['c029_current_first_residual']
assert g['evaluate_aptness_enabled'] is s['summary']['c029_consumer_adequate']
assert r['summary'] == s['summary']
print(
    'SLR_FRAGMENT_EVIDENCE_CONTRACTION_VALIDATION '
    f"fragments={s['summary']['fragments']} "
    f"attribution_source_paid={s['summary']['attribution_source_paid']} "
    f"payment_receipts={s['summary']['payment_receipt_count']} "
    f"paid_obligations={s['summary']['paid_obligation_count']} "
    f"partial_or_nonpaying={s['summary']['partial_or_nonpaying_receipt_count']} "
    f"c029_adequate={str(s['summary']['c029_consumer_adequate']).lower()} "
    f"c029_first_residual={s['summary']['c029_current_first_residual']} "
    'historical_residuals_rewritten=false whole_claim_extent_paid=false '
    'candidate_only=true semantic_promotion=false'
)
PY

cat "$ERR"
printf 'contracted_world=%s\nsidecar=%s\nderived_gates=%s\nreport=%s\nstderr=%s\n' \
  "$OUT_MODEL" "$OUT_SIDECAR" "$OUT_GATES" "$OUT_REPORT" "$ERR"
