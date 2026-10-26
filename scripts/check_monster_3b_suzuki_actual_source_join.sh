#!/usr/bin/env bash
# Runs the two ORIGINAL source paths and their EXISTING exact consumers.
# Expected from repository root with GAP, CTblLib and the original BW fusions.
# A passing source-relative join is not source authentication, a normalizer
# intertwiner, or an Agda/Lean kernel theorem.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v gap >/dev/null || { echo "GAP + CTblLib required" >&2; exit 1; }
mkdir -p build
python3 -m py_compile \
  scripts/render_monster_3b_suzuki_main_quotient_match.py \
  scripts/monster_3b_suzuki_all_conductors_character_audit.py \
  scripts/monster_3b_suzuki_selected_character_join.py

# Source-selected main -> MN3B -> actual Monster restriction.
bash scripts/check_monster_3b_suzuki_main_quotient_match.sh

# Independently extract the complete (all cyclotomic conductors) 6.Suz data.
gap -q scripts/monster_3b_suzuki_all_conductors_export.g
test -s build/monster_3b_suzuki_all_conductors_characters.json

python3 scripts/monster_3b_suzuki_all_conductors_character_audit.py \
  build/monster_3b_suzuki_all_conductors_characters.json \
  --out build/monster_3b_suzuki_all_conductors_audit.json

# Recompute BOTH original validators; check literal class signatures and
# Irr positions, central phase/C2, all-class Sym^2/dual and source selection.
python3 scripts/monster_3b_suzuki_selected_character_join.py \
  build/monster_3b_suzuki_all_conductors_characters.json \
  build/monster_3b_suzuki_main_quotient_match.json \
  --out build/monster_3b_suzuki_selected_join.json

python3 - <<'PY'
import json
from pathlib import Path
p = Path("build/monster_3b_suzuki_selected_join.json")
j = json.loads(p.read_text())
assert j["status"] == "SOURCE_RELATIVE_CHARACTER_JOIN_PASS"
assert j["complete_source_class_signature_matched"] is True
assert j["source_orthogonality_recomputed"] is True
assert j["original_source_authenticated"] is False
assert j["GAP_executed_by_this_check"] is False
assert j["same_object_Monster_intertwiner_proved"] is False
print("PASS: source-relative exact character join; absolute phase/lift/kernel still open")
PY
