#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

OUT="$(mktemp)"
trap 'rm -f "$OUT"' EXIT

python3 scripts/run_vfx_coupled_physics_fixture.py --output "$OUT"
python3 - "$OUT" <<'PY'
import json
import math
import sys

with open(sys.argv[1], encoding="utf-8") as f:
    d = json.load(f)

assert d["status"] == "toy_fixture_not_calibrated"
assert d["boundaries"]["looks_right_proves_physics"] is False
assert d["boundaries"]["wake_proxy_is_full_free_surface_ns"] is False
assert d["boundaries"]["finite_vfx_solve_requires_ns_clay_proof"] is False
assert d["boundaries"]["ordinary_em_requires_yang_mills_clay_proof"] is False
assert d["electromagnetism"]["material_effect_computed"] is False
assert abs(d["contact"]["momentum_residual_kg_m_s"]) < 1e-6
assert abs(d["fluid_air_step"]["momentum_residual_kg_m_s"]) < 1e-5
assert d["contact"]["contact_dissipation_j"] >= 0.0
assert d["fluid_air_step"]["water_drag_n"] >= 0.0
assert d["fluid_air_step"]["air_drag_n"] >= 0.0
assert len(d["artifact_sha256"]) == 64
PY

if command -v agda >/dev/null 2>&1; then
  AGDA_STDLIB="${AGDA_STDLIB:-/usr/share/agda-stdlib}"
  agda -i . -i "$AGDA_STDLIB" DASHI/Physics/VFX/CoupledPhysicalShotExact.agda
  agda -i . -i "$AGDA_STDLIB" DASHI/Physics/VFX/Everything.agda
fi

echo "VFX coupled-physics focused gate passed"
