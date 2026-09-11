#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
SENSIBLAW_ROOT="${2:-/home/c/Documents/code/SensibLaw}"
OUT_DIR="${3:-$HANDOFF_ROOT/gwb-world}"
CERT="$HANDOFF_ROOT/gwb-full-certification.json"
PROJECTION="$HANDOFF_ROOT/gwb-projection/source_projection.json"
WORLD="$OUT_DIR/sensiblaw-gwb-candidate-world-model.json"
NORMALIZED="$OUT_DIR/sensiblaw-gwb-candidate-world-model-normalized.json"
ERR="$OUT_DIR/sensiblaw-gwb-candidate-world.stderr"
PARITY_ERR="$OUT_DIR/sensiblaw-gwb-world-parity.stderr"

[[ -s "$CERT" ]] || { echo "ERROR: missing GWB certification $CERT" >&2; exit 1; }
[[ -s "$PROJECTION" ]] || { echo "ERROR: missing GWB projection manifest $PROJECTION" >&2; exit 1; }
mkdir -p "$OUT_DIR"

python3 "$HERE/slr_gwb_candidate_world.py" \
  --certification "$CERT" \
  --projection-manifest "$PROJECTION" \
  --output "$WORLD" \
  2> "$ERR"

grep -q 'schema=slr-gwb-candidate-world-v1' "$ERR" || {
  echo 'ERROR: GWB CandidateWorldModel receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'raw_text_embedded=false' "$ERR" || {
  echo 'ERROR: GWB world attempted to embed raw/projected text' >&2
  exit 1
}
grep -q 'candidate_only=true' "$ERR" || {
  echo 'ERROR: GWB world candidate-only firewall missing' >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$ERR" || {
  echo 'ERROR: GWB world semantic-promotion firewall missing' >&2
  exit 1
}

# SensibLaw normalizes status_counts by dropping zero-valued classes. Canonicalize
# the producer to that representation before strict parity; this changes no
# candidate semantics and only removes empty bookkeeping coordinates.
python3 - "$WORLD" <<'PY'
import json, sys
from pathlib import Path
p = Path(sys.argv[1])
m = json.loads(p.read_text(encoding='utf-8'))
counts = m.get('status_counts') or {}
m['status_counts'] = {str(k): int(v) for k, v in counts.items() if int(v) != 0}
p.write_text(json.dumps(m, indent=2, sort_keys=True) + '\n', encoding='utf-8')
PY

python3 - "$WORLD" <<'PY'
import json, sys
m = json.load(open(sys.argv[1], encoding='utf-8'))
assert m['schema_version'] == 'sl.candidate_world_model.v0_1'
assert m['lane_family'] == 'slr_document_corpus'
assert m['source_mode'] == 'gwb_certified_projection_receipt'
assert m['model_status'] == 'candidate'
assert m['metadata']['raw_or_projected_text_embedded'] is False
assert m['metadata']['canonical_claim_identity_attached'] is False
assert m['metadata']['speaker_quote_gold_attached'] is False
assert m['metadata']['world_constraints_attached'] is False
assert m['metadata']['candidate_only'] is True
assert m['metadata']['semantic_promotion'] is False
assert m['summary']['sentence_candidate_count'] == 41134
assert m['summary']['sentence_adjacency_relation_count'] == 41124
assert m['summary']['provenance_document_count'] == 10
assert m['summary']['source_family_count'] == 2
assert len(m['claims']) == 41134
assert len(m['relations']) == 41124
assert len(m['provenance_graph']) == 10
assert m['status_counts'] == {'candidate': 82258}
print(
    'SLR_GWB_CANDIDATE_WORLD_VALIDATION '
    f"sentences={len(m['claims'])} relations={len(m['relations'])} "
    f"provenance={len(m['provenance_graph'])} source_families={m['summary']['source_family_count']} "
    'zero_status_classes_omitted=true raw_text_embedded=false candidate_only=true semantic_promotion=false'
)
PY

PARITY_STATUS="not-run"
if [[ -d "$SENSIBLAW_ROOT/src" ]]; then
  PYTHONPATH="$SENSIBLAW_ROOT${PYTHONPATH:+:$PYTHONPATH}" \
  python3 - "$WORLD" "$NORMALIZED" 2> "$PARITY_ERR" <<'PY'
import json, sys
from pathlib import Path
from src.policy.world_model import normalize_world_model

source_path = Path(sys.argv[1])
normalized_path = Path(sys.argv[2])
source = json.loads(source_path.read_text(encoding='utf-8'))
normalized = normalize_world_model(source)
normalized_path.write_text(json.dumps(normalized, indent=2, sort_keys=True) + '\n', encoding='utf-8')

for key in (
    'schema_version','model_id','lane_family','model_status','source_mode',
    'entities','claims','relations','events','timelines','authority_surfaces',
    'provenance_graph','conflicts','residuals','update_rules','projections',
    'external_graph_views','external_bridge_candidates','external_bridge_decisions',
    'external_pressure_results','metadata','summary','status_counts',
):
    assert normalized[key] == source[key], f'normalization drift in {key}'
print(
    'SLR_GWB_SENSIBLAW_PARITY_RECEIPT '
    f"target={normalized['schema_version']} claims={len(normalized['claims'])} "
    f"relations={len(normalized['relations'])} provenance={len(normalized['provenance_graph'])} "
    'normalization_drift=false zero_status_classes_omitted=true candidate_only=true semantic_promotion=false',
    file=sys.stderr,
)
PY
  grep -q 'normalization_drift=false' "$PARITY_ERR" || {
    echo 'ERROR: GWB SensibLaw normalization parity failed' >&2
    cat "$PARITY_ERR" >&2
    exit 1
  }
  PARITY_STATUS="passed"
fi

cat "$ERR"
[[ -s "$PARITY_ERR" ]] && cat "$PARITY_ERR"
printf 'gwb_world=%s\nnormalized=%s\nnormalization_parity=%s\n' "$WORLD" "$NORMALIZED" "$PARITY_STATUS"
