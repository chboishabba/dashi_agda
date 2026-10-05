#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required" >&2
  exit 1
}

mkdir -p build
gap -q scripts/twob_tate276_m24_brauer_character_screen.g

test -s build/twob_tate276_m24_brauer_character_screen.json

python3 - <<'PY'
import json
from pathlib import Path

p = Path("build/twob_tate276_m24_brauer_character_screen.json")
data = json.loads(p.read_text())

assert data["m24_order"] == 244823040
assert data["duad_degree"] == 276
assert data["monster_v2_degree"] == 196884
assert data["central_2b_monster_class_position"] == 3
assert data["two_regular_class_count"] > 0
assert len(data["rows"]) == data["two_regular_class_count"]
assert data["all_lift_traces_independent"] is True
assert data["all_two_regular_traces_match_duad276"] is True

for row in data["rows"]:
    assert row["order"] % 2 == 1
    assert row["odd_lift_count"] >= 1
    assert row["lift_trace_independent"] is True
    assert row["matches"] is True
    assert row["duad_trace"] == row["tate_trace_candidate"]
    assert len(row["lift_rows"]) == row["odd_lift_count"]

print("2B Tate-276 / M24 duad 2-regular character screen PASS")
print("2-regular M24 classes checked:", data["two_regular_class_count"])
for row in data["rows"]:
    print(
        "M24 class", row["m24_class_position"],
        "order", row["order"],
        "Co1", row["co1_class_position"],
        "trace", row["tate_trace_candidate"],
        "duad", row["duad_trace"],
        "lifts", row["odd_lift_count"],
    )
print("JSON:")
print(p.read_text())
PY
