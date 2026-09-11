#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
UNLABELLED="${1:-$HERE/specimens/9-sept-8-03pm-unlabelled}"
WORLD="${UNLABELLED}/sensiblaw-candidate-world-model-with-claims.json"
PATHS="${UNLABELLED}/abc730-labelled-discourse-path.json"
SOURCE="${UNLABELLED}/source.txt"
OUT="${UNLABELLED}/sensiblaw-candidate-world-model-with-claim-fragments.json"
ERR="${UNLABELLED}/sensiblaw-claim-fragment-projection.stderr"

[[ -s "$WORLD" ]] || { echo "ERROR: missing world-with-claims $WORLD" >&2; exit 1; }
[[ -s "$PATHS" ]] || { echo "ERROR: missing discourse paths $PATHS" >&2; exit 1; }
[[ -s "$SOURCE" ]] || { echo "ERROR: missing source $SOURCE" >&2; exit 1; }

python3 "$HERE/slr_claim_fragment_projection.py" \
  --world "$WORLD" \
  --paths "$PATHS" \
  --source "$SOURCE" \
  --output "$OUT" \
  2> "$ERR"

grep -q 'schema=slr-claim-fragment-projection-v1' "$ERR" || {
  echo 'ERROR: claim fragment projection receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'whole_claim_extent_paid=false' "$ERR" || {
  echo 'ERROR: local fragment promoted to whole-claim span' >&2
  exit 1
}
grep -q 'intermediate_speaker_segments_retained=true' "$ERR" || {
  echo 'ERROR: intermediate speaker segment was not retained' >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$ERR" || {
  echo 'ERROR: semantic promotion attempted' >&2
  exit 1
}

python3 - "$OUT" <<'PY'
import json, sys
m = json.load(open(sys.argv[1], encoding='utf-8'))
assert m['schema_version'] == 'sl.candidate_world_model.v0_1'
meta = m['metadata']['claim_fragment_projection']
assert meta['schema'] == 'slr-claim-fragment-projection-v1'
assert meta['whole_claim_extent_paid'] is False
assert meta['intermediate_speaker_segments_retained'] is True
assert meta['skip_intermediate_speaker_forbidden'] is True
assert meta['semantic_promotion'] is False
assert meta['claim_truth_promoted'] is False
print(
    'SLR_CLAIM_FRAGMENT_PROJECTION_VALIDATION '
    f"claim_fragments={m['summary']['claim_fragment_node_count']} "
    f"intermediate_fragments={m['summary']['intermediate_discourse_fragment_count']} "
    f"edges={m['summary']['claim_fragment_projection_edge_count']} "
    f"exact_boundary_fragments={m['summary']['exact_boundary_fragment_count']} "
    f"bounded_boundary_fragments={m['summary']['bounded_boundary_fragment_count']} "
    'whole_claim_extent_paid=false candidate_only=true semantic_promotion=false'
)
PY

cat "$ERR"
printf 'world_with_claim_fragments=%s\nstderr=%s\n' "$OUT" "$ERR"
