#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required" >&2
  exit 1
}

mkdir -p build

gap -q scripts/m24_276_to_m22_f2_composition_screen.g

test -s build/m24_276_to_m22_f2_composition_screen.json

python3 - <<'PY'
import json
from pathlib import Path

p = Path("build/m24_276_to_m22_f2_composition_screen.json")
data = json.loads(p.read_text())

assert data["m24_order"] == 244823040
assert data["permutation_degree"] == 276
assert data["m22d2_order"] == 887040
assert data["m22_order"] == 443520
assert data["m22d2_dimension_sum"] == 276
assert data["m22_dimension_sum"] == 276
assert sum(data["m22d2_orbit_sizes"]) == 276
assert sum(data["m22_orbit_sizes"]) == 276
assert data["m22d2_ten_factor_count"] == data["m22d2_factor_dimensions"].count(10)
assert data["m22_ten_factor_count"] == data["m22_factor_dimensions"].count(10)
assert len(data["m22_ten_factor_atlasrep_matches"]) == data["m22_ten_factor_count"]
for labels in data["m22_ten_factor_atlasrep_matches"]:
    assert labels, "every observed 10d M22 factor must identify with an AtlasRep f2r10 module"
    assert all("f2r10" in label for label in labels)

print("M22:2 orbit sizes:", data["m22d2_orbit_sizes"])
print("M22 orbit sizes:", data["m22_orbit_sizes"])
print("M22:2 F2 factor dimensions:", data["m22d2_factor_dimensions"])
print("M22 F2 factor dimensions:", data["m22_factor_dimensions"])
print("M22:2 10d factor count:", data["m22d2_ten_factor_count"])
print("M22 10d factor count:", data["m22_ten_factor_count"])
print("M22 10d AtlasRep matches:", data["m22_ten_factor_atlasrep_matches"])
PY
