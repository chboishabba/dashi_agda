#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
SPECIMEN="${1:-$HERE/specimens/abc730-2026-09-09-primary}"
BASE_MODEL="${SPECIMEN}/sensiblaw-candidate-world-model.json"
MANIFEST="${SPECIMEN}/source.json"
OUT_MODEL="${SPECIMEN}/sensiblaw-candidate-world-model-constrained.json"
OUT_FIBRES="${SPECIMEN}/world-constraint-fibres.json"
ERR="${SPECIMEN}/world-constraint-fibres.stderr"

[[ -s "$MANIFEST" ]] || { echo "ERROR: missing source manifest $MANIFEST" >&2; exit 1; }
[[ -s "$BASE_MODEL" ]] || bash "$HERE/run_sensiblaw_world_adapter.sh" "$SPECIMEN" >/dev/null

BASE_SHA_BEFORE="$(sha256sum "$BASE_MODEL" | awk '{print $1}')"
python3 "$HERE/slr_world_constraint_fibre.py" \
  --world-model "$BASE_MODEL" \
  --source-manifest "$MANIFEST" \
  --output-model "$OUT_MODEL" \
  --output-fibres "$OUT_FIBRES" \
  2> "$ERR"
BASE_SHA_AFTER="$(sha256sum "$BASE_MODEL" | awk '{print $1}')"

[[ "$BASE_SHA_BEFORE" == "$BASE_SHA_AFTER" ]] || {
  echo "ERROR: base candidate model was rewritten" >&2
  exit 1
}

grep -q 'schema=slr-world-constraint-fibre-v1' "$ERR" || {
  echo 'ERROR: world constraint receipt missing or stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'scalar_score=false' "$ERR" || { echo 'ERROR: scalar-score firewall missing' >&2; exit 1; }
grep -q 'append_only=true' "$ERR" || { echo 'ERROR: append-only firewall missing' >&2; exit 1; }
grep -q 'semantic_promotion=false' "$ERR" || { echo 'ERROR: semantic-promotion firewall missing' >&2; exit 1; }

python3 - "$BASE_MODEL" "$OUT_MODEL" "$OUT_FIBRES" <<'PY'
import json
import sys
from pathlib import Path

base = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
model = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
fibres = json.loads(Path(sys.argv[3]).read_text(encoding="utf-8"))
assert base["schema_version"] == "sl.candidate_world_model.v0_1"
assert model["schema_version"] == base["schema_version"]
assert model["model_id"] == base["model_id"]
assert model["model_status"] == "candidate"
assert model["metadata"]["world_constraint_status"] == "attached-candidate-only"
assert model["metadata"]["world_constraint_schema"] == "slr-world-constraint-fibre-v1"
assert model["metadata"]["world_constraint_scalar_score"] is False
assert model["metadata"]["semantic_promotion"] is False
assert model["metadata"]["candidate_only"] is True
assert model["authority_surfaces"] == base["authority_surfaces"] == []
assert fibres["schema"] == "slr-world-constraint-fibre-v1"
assert fibres["candidate_only"] is True
assert fibres["semantic_promotion"] is False
assert fibres["scalar_score"] is False
assert fibres["append_only"] is True
assert len(fibres["constraint_fibres"]) == len(base["claims"]) + len(base["relations"])
assert all(row["truth_promoted"] is False for row in fibres["constraint_fibres"])
assert all("dimensions" in row for row in fibres["constraint_fibres"])
print(
    "SLR_WORLD_CONSTRAINT_VALIDATION "
    f"model_id={model['model_id']} fibres={len(fibres['constraint_fibres'])} "
    f"compatible={fibres['summary']['compatible_count']} vetoed={fibres['summary']['vetoed_count']} "
    "base_rewritten=false scalar_score=false candidate_only=true"
)
PY

printf 'constrained_world_model=%s\nworld_constraint_fibres=%s\nstderr=%s\n' \
  "$OUT_MODEL" "$OUT_FIBRES" "$ERR"
