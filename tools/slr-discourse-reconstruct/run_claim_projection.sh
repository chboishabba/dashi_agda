#!/usr/bin/env bash
set -euo pipefail

SPECIMEN="${1:-$(dirname "$0")/specimens/abc730-2026-09-09-primary}"
HERE="$(cd "$(dirname "$0")" && pwd)"
WORLD="${SPECIMEN}/sensiblaw-candidate-world-model.json"
SOURCE="${SPECIMEN}/source.txt"
SOURCE_META="${SPECIMEN}/source.json"
OUT="${SPECIMEN}/sensiblaw-candidate-world-model-with-claims.json"
ERR="${SPECIMEN}/sensiblaw-claim-projection.stderr"
FIXTURE="$HERE/../../fixtures/slr/abc730-west-bank-sanctions-2026-09-09-speaker-resolution.jsonl"
CUTS="$HERE/../../fixtures/slr/abc730-west-bank-sanctions-2026-09-09-intrasentence-cuts.jsonl"

[[ -s "$WORLD" ]] || bash "$HERE/run_sensiblaw_world_adapter.sh" "$SPECIMEN" >/dev/null
[[ -s "$FIXTURE" ]] || { echo "ERROR: missing fixture $FIXTURE" >&2; exit 1; }
[[ -s "$CUTS" ]] || { echo "ERROR: missing cut fixture $CUTS" >&2; exit 1; }

args=(
  --world "$WORLD"
  --fixture "$FIXTURE"
  --cuts "$CUTS"
  --output "$OUT"
)
SOURCE_MODE="sentence-mapping-only"
if [[ -s "$SOURCE" && -s "$SOURCE_META" ]]; then
  args+=(--source "$SOURCE" --source-metadata "$SOURCE_META")
  SOURCE_MODE="same-source-refinement"
elif [[ -s "$SOURCE" || -s "$SOURCE_META" ]]; then
  echo "ERROR: source/source-metadata must either both exist or both be absent" >&2
  exit 1
fi

python3 "$HERE/slr_claim_projection.py" "${args[@]}" 2> "$ERR"

grep -q 'schema=slr-canonical-claim-projection-v2' "$ERR" || {
  echo 'ERROR: canonical claim projection receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'historical_fixture_speaker_is_authority=false' "$ERR" || {
  echo 'ERROR: historical fixture speaker status imported as authority' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$ERR" || {
  echo 'ERROR: claim projection attempted semantic promotion' >&2
  cat "$ERR" >&2
  exit 1
}

python3 - "$OUT" "$SOURCE_MODE" <<'PY'
import json, sys
m = json.load(open(sys.argv[1], encoding='utf-8'))
source_mode = sys.argv[2]
assert m['schema_version'] == 'sl.candidate_world_model.v0_1'
meta = m['metadata']['canonical_claim_projection']
assert meta['schema'] == 'slr-canonical-claim-projection-v2'
assert meta['historical_fixture_speaker_status_is_authority'] is False
assert meta['primary_speaker_resolution_is_claim_relative'] is True
assert meta['exact_subspan_weld_paid_only_by_same_source_unique_phrase_offsets'] is True
assert meta['semantic_promotion'] is False
assert meta['candidate_only'] is True
if source_mode == 'sentence-mapping-only':
    assert meta['source'] == 'unsupplied'
    assert m['summary']['exact_subspan_projection_edge_count'] == 0
print(
    'SLR_CLAIM_PROJECTION_INTEGRITY '
    f"source_mode={source_mode} "
    f"claims={m['summary']['canonical_claim_reference_count']} "
    f"edges={m['summary']['candidate_claim_projection_edge_count']} "
    f"exact_edges={m['summary']['exact_subspan_projection_edge_count']} "
    f"exact_claims={m['summary']['exact_subspan_claim_count']} "
    f"unresolved_exact={m['summary']['unresolved_exact_subspan_claim_count']} "
    f"ambiguous_edges={m['summary']['ambiguous_sentence_projection_edge_count']} "
    f"cuts={m['summary']['claim_projection_cut_constraint_count']} "
    f"target_schema={m['schema_version']} candidate_only=true semantic_promotion=false"
)
PY

printf 'source_mode=%s\nworld_with_claims=%s\nstderr=%s\n' "$SOURCE_MODE" "$OUT" "$ERR"
