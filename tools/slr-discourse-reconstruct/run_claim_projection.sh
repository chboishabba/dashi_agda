#!/usr/bin/env bash
set -euo pipefail

SPECIMEN="${1:-/tmp/slr-specimens/9-sept-8-03pm}"
HERE="$(cd "$(dirname "$0")" && pwd)"
WORLD="${SPECIMEN}/sensiblaw-candidate-world-model.json"
OUT="${SPECIMEN}/sensiblaw-candidate-world-model-with-claims.json"
ERR="${SPECIMEN}/sensiblaw-claim-projection.stderr"
FIXTURE="$HERE/../../fixtures/slr/abc730-west-bank-sanctions-2026-09-09-speaker-resolution.jsonl"
CUTS="$HERE/../../fixtures/slr/abc730-west-bank-sanctions-2026-09-09-intrasentence-cuts.jsonl"

[[ -s "$WORLD" ]] || bash "$HERE/run_sensiblaw_world_adapter.sh" "$SPECIMEN" >/dev/null
[[ -s "$FIXTURE" ]] || { echo "ERROR: missing fixture $FIXTURE" >&2; exit 1; }
[[ -s "$CUTS" ]] || { echo "ERROR: missing cut fixture $CUTS" >&2; exit 1; }

python3 "$HERE/slr_claim_projection.py" \
  --world "$WORLD" \
  --fixture "$FIXTURE" \
  --cuts "$CUTS" \
  --output "$OUT" \
  2> "$ERR"

grep -q 'schema=slr-canonical-claim-projection-v1' "$ERR" || {
  echo 'ERROR: canonical claim projection receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'exact_span_weld_default=unpaid' "$ERR" || {
  echo 'ERROR: claim projection unexpectedly promotes exact span weld' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'fixture_speaker_status_is_authority=false' "$ERR" || {
  echo 'ERROR: stale fixture speaker status imported as authority' >&2
  cat "$ERR" >&2
  exit 1
}

python3 - "$OUT" <<'PY'
import json, sys
p = sys.argv[1]
m = json.load(open(p, encoding='utf-8'))
assert m['schema_version'] == 'sl.candidate_world_model.v0_1'
meta = m['metadata']['canonical_claim_projection']
assert meta['schema'] == 'slr-canonical-claim-projection-v1'
assert meta['fixture_speaker_status_is_authority'] is False
assert meta['exact_subspan_weld_default'] == 'unpaid'
assert meta['semantic_promotion'] is False
assert meta['candidate_only'] is True
print(f"SLR_CLAIM_PROJECTION_INTEGRITY claims={m['summary']['canonical_claim_reference_count']} edges={m['summary']['candidate_claim_projection_edge_count']} ambiguous_edges={m['summary']['ambiguous_sentence_projection_edge_count']} cuts={m['summary']['claim_projection_cut_constraint_count']} target_schema={m['schema_version']} candidate_only=true semantic_promotion=false")
PY

printf 'world_with_claims=%s\nstderr=%s\n' "$OUT" "$ERR"
