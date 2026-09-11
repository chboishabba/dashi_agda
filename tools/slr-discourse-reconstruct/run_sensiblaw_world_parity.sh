#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
SPECIMEN="${1:-/tmp/slr-specimens/9-sept-8-03pm}"
SENSIBLAW_ROOT="${2:-/home/c/Documents/code/SensibLaw}"
WORLD="${SPECIMEN}/sensiblaw-candidate-world-model.json"
NORMALIZED="${SPECIMEN}/sensiblaw-candidate-world-model-normalized.json"
ERR="${SPECIMEN}/sensiblaw-world-parity.stderr"

[[ -d "$SENSIBLAW_ROOT/src" ]] || {
  echo "ERROR: missing SensibLaw checkout at $SENSIBLAW_ROOT" >&2
  exit 1
}

bash "$HERE/run_sensiblaw_world_adapter.sh" "$SPECIMEN" >/dev/null

PYTHONPATH="$SENSIBLAW_ROOT${PYTHONPATH:+:$PYTHONPATH}" \
python3 - "$WORLD" "$NORMALIZED" > /dev/null 2> "$ERR" <<'PY'
import json
import sys
from pathlib import Path

from src.policy.world_model import normalize_world_model

source_path = Path(sys.argv[1])
normalized_path = Path(sys.argv[2])
source = json.loads(source_path.read_text(encoding="utf-8"))
normalized = normalize_world_model(source)
normalized_path.write_text(json.dumps(normalized, indent=2, sort_keys=True) + "\n", encoding="utf-8")

assert normalized["schema_version"] == "sl.candidate_world_model.v0_1"
assert normalized["model_id"] == source["model_id"]
assert normalized["lane_family"] == source["lane_family"]
assert normalized["model_status"] == source["model_status"]
assert normalized["source_mode"] == source["source_mode"]
for key in (
    "entities",
    "claims",
    "relations",
    "events",
    "timelines",
    "authority_surfaces",
    "provenance_graph",
    "conflicts",
    "residuals",
    "update_rules",
    "projections",
    "external_graph_views",
    "external_bridge_candidates",
    "external_bridge_decisions",
    "external_pressure_results",
):
    assert normalized[key] == source[key], f"normalization drift in {key}"
assert normalized["metadata"] == source["metadata"]
assert normalized["summary"] == source["summary"]
assert normalized["status_counts"] == source["status_counts"]

print(
    "SLR_SENSIBLAW_WORLD_PARITY_RECEIPT "
    f"schema={source['metadata']['adapter_schema']} "
    f"target={normalized['schema_version']} "
    f"claims={len(normalized['claims'])} relations={len(normalized['relations'])} "
    f"conflicts={len(normalized['conflicts'])} residuals={len(normalized['residuals'])} "
    "normalization_drift=false candidate_only=true semantic_promotion=false",
    file=sys.stderr,
)
PY

grep -q 'SLR_SENSIBLAW_WORLD_PARITY_RECEIPT' "$ERR" || {
  echo 'ERROR: SensibLaw normalization parity receipt missing' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'normalization_drift=false' "$ERR" || {
  echo 'ERROR: SensibLaw normalization drift detected' >&2
  cat "$ERR" >&2
  exit 1
}

printf 'world_model=%s\nnormalized=%s\nstderr=%s\n' "$WORLD" "$NORMALIZED" "$ERR"
