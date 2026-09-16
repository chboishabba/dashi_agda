#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
SPECIMEN="${1:-/tmp/slr-specimens/9-sept-8-03pm}"
SPANS="${SPECIMEN}/discourse-spans-transcript-wide.tsv"
QUALITY="${SPECIMEN}/discourse-quality-transcript-wide.tsv"
ROLES="${SPECIMEN}/role-transitions-transcript-wide.tsv"
SOURCE="${SPECIMEN}/source.txt"
SOURCE_SHA_FILE="${SPECIMEN}/source.sha256"
OUT="${SPECIMEN}/sensiblaw-candidate-world-model.json"
ERR="${SPECIMEN}/sensiblaw-candidate-world-model.stderr"

[[ -s "$SOURCE" ]] || { echo "ERROR: missing source $SOURCE" >&2; exit 1; }
[[ -s "$SPANS" ]] || bash "$HERE/run_span_reconstruction.sh" "$SPECIMEN" >/dev/null
[[ -s "$QUALITY" ]] || bash "$HERE/run_discourse_quality.sh" "$SPECIMEN" >/dev/null
[[ -s "$ROLES" ]] || bash "$HERE/run_role_transitions.sh" "$SPECIMEN" >/dev/null

if [[ -s "$SOURCE_SHA_FILE" ]]; then
  SOURCE_SHA="$(awk 'NR==1 {print $1}' "$SOURCE_SHA_FILE")"
else
  SOURCE_SHA="$(sha256sum "$SOURCE" | awk '{print $1}')"
fi
SOURCE_REF="source:${SOURCE_SHA}"
MODEL_ID="slr:$(basename "$SPECIMEN"):${SOURCE_SHA:0:16}"

python3 "$HERE/slr_sensiblaw_world_adapter.py" \
  --spans "$SPANS" \
  --quality "$QUALITY" \
  --roles "$ROLES" \
  --output "$OUT" \
  --model-id "$MODEL_ID" \
  --source-ref "$SOURCE_REF" \
  --source-sha256 "$SOURCE_SHA" \
  2> "$ERR"

grep -q 'schema=slr-sensiblaw-world-adapter-v1' "$ERR" || {
  echo 'ERROR: SLR/SensibLaw adapter receipt missing or stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'target=sl.candidate_world_model.v0_1' "$ERR" || {
  echo 'ERROR: target CandidateWorldModel schema mismatch' >&2
  cat "$ERR" >&2
  exit 1
}

python3 - "$OUT" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
model = json.loads(path.read_text(encoding="utf-8"))
assert model["schema_version"] == "sl.candidate_world_model.v0_1"
assert model["lane_family"] == "slr_discourse"
assert model["model_status"] == "candidate"
assert model["metadata"]["adapter_schema"] == "slr-sensiblaw-world-adapter-v1"
assert model["metadata"]["candidate_only"] is True
assert model["metadata"]["semantic_promotion"] is False
assert model["metadata"]["world_constraint_status"] == "not_attached"
assert model["authority_surfaces"] == []
assert all(row.get("promotion_status") == "candidate_only" for row in model["claims"])
assert all(row.get("promotion_status") == "candidate_only" for row in model["relations"])
expected_candidate = sum(row.get("status") == "candidate" for row in model["claims"])
expected_candidate += sum(row.get("status") == "candidate" for row in model["relations"])
expected_conflicted = sum(row.get("status") == "conflicted" for row in model["claims"])
assert model["status_counts"].get("candidate", 0) == expected_candidate
assert model["status_counts"].get("conflicted", 0) == expected_conflicted
print(
    "SLR_SENSIBLAW_WORLD_ADAPTER_VALIDATION "
    f"model_id={model['model_id']} claims={len(model['claims'])} "
    f"relations={len(model['relations'])} conflicts={len(model['conflicts'])} "
    f"residuals={len(model['residuals'])} candidate_only=true"
)
PY

printf 'world_model=%s\nstderr=%s\n' "$OUT" "$ERR"
