#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required for Suzuki/main quotient same-object matching" >&2
  exit 1
}

mkdir -p build/generated/DASHI/Moonshine/Generated
python -m py_compile scripts/render_monster_3b_suzuki_main_quotient_match.py

gap -q scripts/monster_3b_suzuki_main_quotient_match.g

test -s build/monster_3b_suzuki_main_quotient_match.json

python scripts/render_monster_3b_suzuki_main_quotient_match.py \
  build/monster_3b_suzuki_main_quotient_match.json \
  build/generated/DASHI/Moonshine/Generated/Monster3BSuzukiMainQuotientMatchCertificate.agda

test -s build/generated/DASHI/Moonshine/Generated/Monster3BSuzukiMainQuotientMatchCertificate.agda

python - <<'PY'
import json
from pathlib import Path
p = json.loads(Path("build/monster_3b_suzuki_main_quotient_match.json").read_text())
assert p["main_table"] == "3^1+12:6.Suz.2"
assert p["six_suz_table"] == "6.Suz"
assert p["six_suz_outer_table"] == "6.Suz.2"
assert p["base_1458_central_trace"] == -729
assert isinstance(p["base_1458_extraspecial_central_class_position"], int)
assert p["base_1458_extraspecial_central_class_position"] > 0
assert isinstance(p["qg_to_n3b_kernel_order_three_class_position"], int)
assert isinstance(p["qg_to_n3b_kernel_outer_class_position"], int)
# Primary Barraclough--Wilson supplementary quotient coordinates.  These are
# an external historical-data regression, deliberately separate from the GAP
# semantic selector that recovers the kernel by order/size/quotient identity.
assert p["qg_to_n3b_kernel_order_three_class_position"] == 20
assert p["qg_to_n3b_kernel_outer_class_position"] == 6
assert p["qg_to_n3b_kernel_order_three_class_position"] != p["base_1458_extraspecial_central_class_position"]
assert len(p["degree_12_atlas_labels"]) == 2
assert len(p["degree_78_atlas_labels"]) == 2
assert len(p["main_12_split_positions"]) == 2
assert len(p["main_78_split_positions"]) == 2
assert p["main_12_descending_position"] in p["main_12_split_positions"]
assert p["main_78_descending_position"] in p["main_78_split_positions"]
assert p["mn3b_12_monster_multiplicity"] > 0
assert p["mn3b_78_monster_multiplicity"] > 0
assert p["extraspecial_centre_selected_by_outer_quotient_kernel"] is True
assert p["qg_to_n3b_kernel_class_identified"] is True
assert p["outer_pair_restriction_full_character_match"] is True
assert p["main_product_split_full_character_decomposition"] is True
assert p["quotient_descent_full_character_match"] is True
assert p["restricted_monster_same_object_match"] is True
assert p["diagonal_kernel_orientation_paid"] is False
assert p["individual_zeta_label_orientation_paid"] is False
PY

generated=build/generated/DASHI/Moonshine/Generated/Monster3BSuzukiMainQuotientMatchCertificate.agda
grep -F 'pairFamilyMonsterOccurrencePaid = true' "$generated" >/dev/null
grep -F 'qGtoN3BKernelOrderThreeClassPosition' "$generated" >/dev/null
grep -F 'extraspecialCentralClassPosition' "$generated" >/dev/null
grep -F 'diagonalKernelOrientationPaid = false' "$generated" >/dev/null
grep -F 'individualZetaLabelOrientationPaid = false' "$generated" >/dev/null
grep -F 'twelvePairProductDegree : 1458 * 24 ≡ 2 * 17496' "$generated" >/dev/null
grep -F 'seventyEightPairProductDegree : 1458 * 156 ≡ 2 * 113724' "$generated" >/dev/null

echo "Monster 3B Suzuki/main quotient same-object match checks passed"
