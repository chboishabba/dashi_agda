#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OUT_DIR="${TMPDIR:-/tmp}/dashi_bioacoustic_fly_state_space"
mkdir -p "$OUT_DIR"

python3 scripts/render_state_space_trajectory.py \
  --demo birdsong \
  --out "$OUT_DIR/birdsong.svg" \
  --receipt "$OUT_DIR/birdsong.json"

python3 scripts/render_state_space_trajectory.py \
  --demo fly \
  --out "$OUT_DIR/fly.svg" \
  --receipt "$OUT_DIR/fly.json"

python3 - "$OUT_DIR/birdsong.json" "$OUT_DIR/fly.json" <<'PY'
import json
import sys
from pathlib import Path

bird = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
fly = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))

assert bird["mode"] == "synthetic-birdsong-demo"
assert bird["point_count"] == 240
assert bird["boundary"]["rendered_trajectory_is_scientific_authority"] is False
assert fly["mode"] == "synthetic-fly-sensorimotor-demo"
assert fly["point_count"] == 420
assert fly["channels"] == [
    "behaviour",
    "body",
    "effector",
    "motor",
    "neural",
    "sensory-return",
]
assert fly["boundary"]["visual_proximity_implies_physical_or_anatomical_proximity"] is False
PY

bash scripts/check_bioacoustic_fly_si_units_static.sh
bash scripts/check_bioacoustic_song_energy_static.sh
bash scripts/check_bioacoustic_situated_performance_static.sh
bash scripts/check_bioacoustic_multimodal_episode_static.sh
bash scripts/check_bioacoustic_multimodal_lag_factorisation_static.sh
bash scripts/check_gauthey_external_manifest_static.sh

if command -v agda >/dev/null 2>&1; then
  agda -i . DASHI/Biology/BioacousticFlyStateSpaceValidation.agda
else
  echo "Agda not found; runtime/static checks may pass but kernel check is not claimed." >&2
fi

echo "bioacoustic/fly state-space checks passed"
