#!/usr/bin/env bash
# Original #1098 source witness -> original #1250 CTblLib 4D class weld.
# Run from any checkout of #1250 with a JSON produced by the #1098
# source script (SHA-pinned original ATLAS matrices).
# No full matrix group Size or SylowSubgroup is called.
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo "usage: $0 <#1098-original-ATLAS-rotation-2B-receipt.json>" >&2
  exit 2
fi
test -s "$1" || { echo "missing original #1098 word receipt" >&2; exit 2; }
WORD_RECEIPT="$(realpath "$1")"
cd "$(dirname "$0")/.."
command -v gap >/dev/null || { echo "GAP + CTblLib required" >&2; exit 2; }
mkdir -p build
python3 -m py_compile scripts/monster3b_atlas_d4_word_to_4class_source_weld.py
python3 -m pytest -q tests/test_monster3b_atlas_d4_word_to_4class_source_weld.py
gap -b -q scripts/monster3b_atlas_suz2b_monster_4class_source_fusion.g
python3 scripts/monster3b_atlas_suz2b_monster_4class_receipt_validator.py \
  build/monster3b_atlas_suz2b_monster_4class_source_fusion.json \
  --out build/monster3b_atlas_suz2b_monster_4class_validated.json
python3 scripts/monster3b_atlas_d4_word_to_4class_source_weld.py \
  "$WORD_RECEIPT" build/monster3b_atlas_suz2b_monster_4class_source_fusion.json \
  --out build/monster3b_atlas_d4_word_to_4class_source_weld.json
python3 - <<'PY'
import json
from pathlib import Path
r=json.loads(Path("build/monster3b_atlas_d4_word_to_4class_source_weld.json").read_text())
assert r["status"] == "SOURCE_RELATIVE_ACTUAL_WORD_CLASS_WELD_PASS"
assert r["selected_two_suz_class_position"] == 5
assert r["selected_monster_four_class"] == "4D"
assert r["conditional_phase_trace"] == 66
assert r["actual_Monster_generator_word_produced"] is False
assert r["actual_Monster_Hom_or_VOA_action_paid"] is False
print("PASS: SOURCE-RELATIVE ATLAS D4 WORD -> 2.Suz.2 CLASS 5 -> MONSTER 4D")
print("Open: original quotient-generator intertwiner, absolute phase and Hom action")
PY
