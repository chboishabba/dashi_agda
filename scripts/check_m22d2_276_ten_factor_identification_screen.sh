#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required" >&2
  exit 1
}

mkdir -p build
gap -q scripts/m22d2_276_ten_factor_identification_screen.g

test -s build/m22d2_276_ten_factor_identification_screen.json

python3 - <<'PY'
import json
from pathlib import Path

p = Path("build/m22d2_276_ten_factor_identification_screen.json")
data = json.loads(p.read_text())

assert data["m24_order"] == 244823040
assert data["m22d2_order"] == 887040
assert data["dimension"] == 276
assert data["dimension_sum"] == 276
assert data["ten_factor_count"] == data["factor_dimensions"].count(10)
assert len(data["ten_factor_atlasrep_matches"]) == data["ten_factor_count"]
assert data["ten_factor_count"] > 0, "M22:2 duad-276 must expose at least one 10d factor"
for labels in data["ten_factor_atlasrep_matches"]:
    assert labels, "every 10d M22:2 factor must identify with an AtlasRep 10d module"
assert data["every_ten_factor_identified"] is True
assert data["finite_duad_m22d2_stable_ten_subquotient_identified"] is True
assert data["actual_2b_tate_stable_subquotient_identified"] is False

print("M22:2 duad-276 factor dimensions:", data["factor_dimensions"])
print("10d factor count:", data["ten_factor_count"])
print("10d AtlasRep matches:", data["ten_factor_atlasrep_matches"])
print("finite duad stable 10d subquotient: PASS")
print("actual Tate stable subquotient: intentionally still false")
PY
