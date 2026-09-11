#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
SPECIMEN="${1:-$HERE/specimens/abc730-2026-09-09-primary}"
SOURCE="$SPECIMEN/source.txt"
SOURCE_META="$SPECIMEN/source.json"
WORLD="$SPECIMEN/sensiblaw-candidate-world-model.json"
OUT="$SPECIMEN/canonical-claim-projection.json"
ERR="$SPECIMEN/canonical-claim-projection.stderr"

[[ -s "$SOURCE" ]] || { echo "ERROR: missing $SOURCE" >&2; exit 1; }
[[ -s "$SOURCE_META" ]] || { echo "ERROR: missing $SOURCE_META" >&2; exit 1; }
[[ -s "$WORLD" ]] || bash "$HERE/run_sensiblaw_world_adapter.sh" "$SPECIMEN" >/dev/null

python3 "$HERE/slr_canonical_claim_projection.py" \
  --source "$SOURCE" \
  --source-metadata "$SOURCE_META" \
  --world-model "$WORLD" \
  --output "$OUT" \
  2> "$ERR"

grep -q 'schema=slr-canonical-claim-projection-v1' "$ERR" || {
  echo 'ERROR: canonical claim projection receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$ERR" || {
  echo 'ERROR: claim projection attempted semantic promotion' >&2
  cat "$ERR" >&2
  exit 1
}

python3 - "$OUT" <<'PY'
import json, sys
from pathlib import Path
p = Path(sys.argv[1])
d = json.loads(p.read_text(encoding='utf-8'))
assert d['schema'] == 'slr-canonical-claim-projection-v1'
assert d['target_schema'] == 'sl.candidate_world_model.v0_1'
assert d['semantic_promotion'] is False
assert d['candidate_only'] is True
assert d['rules']['projection_requires_same_source_sha'] is True
assert d['rules']['projection_requires_unique_bounded_source_phrase'] is True
assert d['rules']['lexical_similarity_fallback'] is False
assert d['rules']['projection_promotes_truth'] is False
assert all(x['same_source_object'] is True for x in d['projections'])
assert all(x['bounded_source_phrase_unique'] is True for x in d['projections'])
assert all(x['canonical_claim_truth_promoted'] is False for x in d['projections'])
print(
    'SLR_CANONICAL_CLAIM_PROJECTION_VALIDATION '
    f"projections={d['projection_count']} unresolved={d['unresolved_count']} "
    'same_source_required=true semantic_promotion=false candidate_only=true'
)
PY

printf 'claim_projection=%s\nstderr=%s\n' "$OUT" "$ERR"
