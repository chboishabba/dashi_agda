#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
UNLABELLED="${1:-$HERE/specimens/9-sept-8-03pm-unlabelled}"
WORLD="${UNLABELLED}/sensiblaw-candidate-world-model-with-claim-fragments.json"
RESIDUAL_MAP="${2:-$HERE/specimens/abc730-2026-09-09-primary/canonical-claim-residuals.json}"
OUT="${UNLABELLED}/sensiblaw-candidate-world-model-with-fragment-residuals.json"
ERR="${UNLABELLED}/sensiblaw-claim-fragment-residual-inheritance.stderr"

[[ -s "$WORLD" ]] || bash "$HERE/run_claim_fragment_projection.sh" "$UNLABELLED" >/dev/null
[[ -s "$RESIDUAL_MAP" ]] || { echo "ERROR: missing canonical claim residual map $RESIDUAL_MAP" >&2; exit 1; }

BASE_SHA_BEFORE="$(sha256sum "$WORLD" | awk '{print $1}')"
python3 "$HERE/slr_claim_fragment_residual_inheritance.py" \
  --world "$WORLD" \
  --residual-map "$RESIDUAL_MAP" \
  --output "$OUT" \
  2> "$ERR"
BASE_SHA_AFTER="$(sha256sum "$WORLD" | awk '{print $1}')"

[[ "$BASE_SHA_BEFORE" == "$BASE_SHA_AFTER" ]] || {
  echo 'ERROR: fragment world was rewritten in place' >&2
  exit 1
}

grep -q 'schema=slr-claim-fragment-residual-inheritance-v1' "$ERR" || {
  echo 'ERROR: fragment residual inheritance receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'intermediate_inherits_adjacent_claim=false' "$ERR" || {
  echo 'ERROR: intermediate fragment inherited neighbour claim debt' >&2
  exit 1
}
grep -q 'whole_claim_extent_paid=false' "$ERR" || {
  echo 'ERROR: residual inheritance promoted whole-claim extent' >&2
  exit 1
}
grep -q 'claim_truth_promoted=false' "$ERR" || {
  echo 'ERROR: residual inheritance promoted claim truth' >&2
  exit 1
}
grep -q 'append_only=true' "$ERR" || {
  echo 'ERROR: append-only receipt missing' >&2
  exit 1
}

python3 - "$WORLD" "$OUT" <<'PY'
import json, sys
from pathlib import Path
base = json.loads(Path(sys.argv[1]).read_text(encoding='utf-8'))
out = json.loads(Path(sys.argv[2]).read_text(encoding='utf-8'))
assert base['schema_version'] == out['schema_version'] == 'sl.candidate_world_model.v0_1'
meta = out['metadata']['claim_fragment_residual_inheritance']
assert meta['schema'] == 'slr-claim-fragment-residual-inheritance-v1'
assert meta['claim_local_fragments_inherit_consumer_debt'] is True
assert meta['intermediate_fragments_inherit_adjacent_claim_debt'] is False
assert meta['whole_claim_extent_paid_by_inheritance'] is False
assert meta['claim_truth_promoted_by_inheritance'] is False
assert meta['append_only'] is True
assert meta['semantic_promotion'] is False
assert len(out['claims']) == len(base['claims'])
assert len(out['relations']) == len(base['relations'])
assert len(out['residuals']) >= len(base['residuals'])
for node in out['claims']:
    if node.get('node_kind') == 'intermediate_discourse_fragment':
        inheritance = (node.get('metadata') or {}).get('canonical_claim_residual_inheritance') or {}
        assert inheritance.get('inherited_obligation_ids') == []
print(
    'SLR_CLAIM_FRAGMENT_RESIDUAL_INHERITANCE_VALIDATION '
    f"fragments={out['summary']['claim_fragment_residual_inheritance_fragment_count']} "
    f"mapped_fragments={out['summary']['claim_fragment_residual_inheritance_mapped_fragment_count']} "
    f"intermediate_fragments={out['summary']['claim_fragment_residual_inheritance_intermediate_fragment_count']} "
    f"obligations={out['summary']['claim_fragment_residual_inheritance_obligation_count']} "
    f"unmapped={out['summary']['claim_fragment_residual_inheritance_unmapped_claim_fragment_count']} "
    'append_only=true intermediate_inherits_adjacent_claim=false semantic_promotion=false'
)
PY

cat "$ERR"
printf 'world_with_fragment_residuals=%s\nstderr=%s\n' "$OUT" "$ERR"
