#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
UNLABELLED="${1:-$HERE/specimens/9-sept-8-03pm-unlabelled}"
LABELLED="${2:-$HERE/specimens/abc730-2026-09-09-primary}"
WORLD="${UNLABELLED}/sensiblaw-candidate-world-model-with-claim-fragments.json"
EVIDENCE_MANIFEST="${LABELLED}/source.json"
OUT_MODEL="${UNLABELLED}/sensiblaw-candidate-world-model-fragment-evidence-contracted.json"
OUT_SIDECAR="${UNLABELLED}/fragment-evidence-contractions.json"
ERR="${UNLABELLED}/fragment-evidence-contractions.stderr"

if [[ ! -s "$WORLD" ]]; then
  bash "$HERE/run_claim_fragment_projection.sh" "$UNLABELLED" >/dev/null
fi
[[ -s "$WORLD" ]] || { echo "ERROR: missing fragment world $WORLD" >&2; exit 1; }
[[ -s "$EVIDENCE_MANIFEST" ]] || { echo "ERROR: missing labelled evidence manifest $EVIDENCE_MANIFEST" >&2; exit 1; }

python3 "$HERE/slr_fragment_evidence_contraction.py" \
  --world "$WORLD" \
  --evidence-manifest "$EVIDENCE_MANIFEST" \
  --output-model "$OUT_MODEL" \
  --output-sidecar "$OUT_SIDECAR" \
  2> "$ERR"

grep -q 'schema=slr-fragment-evidence-contraction-v1' "$ERR" || {
  echo 'ERROR: fragment evidence contraction receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'fragment_provenance_is_evidence_authority=false' "$ERR" || {
  echo 'ERROR: fragment provenance conflated with evidence authority' >&2
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

python3 - "$OUT_MODEL" "$OUT_SIDECAR" <<'PY'
import json, sys
m = json.load(open(sys.argv[1], encoding='utf-8'))
s = json.load(open(sys.argv[2], encoding='utf-8'))
assert m['schema_version'] == 'sl.candidate_world_model.v0_1'
meta = m['metadata']['fragment_evidence_contraction']
assert meta['schema'] == 'slr-fragment-evidence-contraction-v1'
assert meta['fragment_provenance_is_evidence_authority'] is False
assert meta['evidence_authority_rewrites_fragment_provenance'] is False
assert meta['whole_claim_extent_paid'] is False
assert meta['claim_truth_promoted'] is False
assert meta['candidate_only'] is True
assert meta['semantic_promotion'] is False
assert s['append_only'] is True
assert s['semantic_promotion'] is False
assert len(s['contractions']) == (
    m['summary']['claim_fragment_node_count'] + m['summary']['intermediate_discourse_fragment_count']
)
print(
    'SLR_FRAGMENT_EVIDENCE_CONTRACTION_VALIDATION '
    f"fragments={s['summary']['fragments']} "
    f"attribution_source_paid={s['summary']['attribution_source_paid']} "
    f"evidence_open={s['summary']['evidence_open']} "
    f"intermediate_fragments={s['summary']['intermediate_fragments']} "
    'fragment_provenance_is_evidence_authority=false '
    'whole_claim_extent_paid=false candidate_only=true semantic_promotion=false'
)
PY

cat "$ERR"
printf 'contracted_world=%s\nsidecar=%s\nstderr=%s\n' "$OUT_MODEL" "$OUT_SIDECAR" "$ERR"
