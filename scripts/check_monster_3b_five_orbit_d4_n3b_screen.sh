#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required for the five-orbit D4/N(3B) screen" >&2
  exit 1
}

mkdir -p build
rm -f build/monster_3b_five_orbit_d4_n3b_screen.json

gap -q scripts/monster_3b_five_orbit_d4_n3b_screen.g

test -s build/monster_3b_five_orbit_d4_n3b_screen.json

# Execute the committed receipt assertions without depending on pytest being
# preinstalled in the GAP/AtlasRep runner image.
python3 - <<'PY'
import importlib.util
from pathlib import Path

path = Path("tests/test_monster_3b_five_orbit_d4_n3b_screen.py")
spec = importlib.util.spec_from_file_location("monster3b_d4_n3b_receipt_tests", path)
assert spec is not None and spec.loader is not None
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

for name in sorted(vars(module)):
    if name.startswith("test_"):
        getattr(module, name)()
PY

python3 - <<'PY'
import json
from pathlib import Path

receipt = json.loads(Path("build/monster_3b_five_orbit_d4_n3b_screen.json").read_text())
assert receipt["target_character"] == [5, 5, 1, 3, 3]
assert receipt["target_multiplicities"] == {"A1": 3, "A2": 0, "B1": 1, "B2": 1, "E": 0}
assert receipt["possible_fusion_count"] >= receipt["character_compatible_fusion_count"] >= 0
assert receipt["possible_fusion_is_actual_subgroup"] is False
assert receipt["character_match_creates_intertwiner"] is False
assert receipt["selected_action_same_object_paid"] is False

if receipt["actual_d4_subgroup_realized"]:
    assert receipt["actual_realized_fusion"] is not None
else:
    assert receipt["actual_realized_fusion"] is None

print(
    "five-orbit D4/N(3B) receipt: possible=", receipt["possible_fusion_count"],
    " compatible=", receipt["character_compatible_fusion_count"],
    " actual-realized=", receipt["actual_d4_subgroup_realized"],
    " actual-compatible=", receipt["actual_character_compatible"],
    sep="",
)
PY
