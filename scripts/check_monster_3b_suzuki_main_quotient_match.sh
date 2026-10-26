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
assert p["base_1458_outer_centre_inverting_trace_zero"] is True
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
assert p["six_suz_group_order"] == 2690072985600
assert p["six_suz_class_count"] == 210
for key in ("six_suz_degree12_positions","six_suz_degree78_positions"):
    rows=p[key]
    assert isinstance(rows,list) and len(rows)==2
    assert all(type(x) is int and 1<=x<=210 for x in rows)
    assert len(set(rows))==2
assert not (
    set(p["six_suz_degree12_positions"]) &
    set(p["six_suz_degree78_positions"])
)

# Source-selected 78 is now chosen by full 6.Suz -> main -> MN3B -> Monster
# character matching, NOT by requiring a faithful degree78 in advance.
assert type(p["source_selected_degree_78_faithful_to_6Suz"]) is bool
assert type(p["suzuki_central_involution_class_position"]) is int
assert p["suzuki_central_involution_class_position"] > 0
assert p["source_selected_S90_central_C2_trace"] in (-90, 66)
assert p["sym2_candidate_S90_central_C2_trace"] == 66
assert p["selected_78_direct_sym2_full_character_pair_count"] in (0, 2)
assert p["selected_78_dual_sym2_full_character_pair_count"] in (0, 2)
assert type(p["selected_78_is_nebe_sym2_family_full_character_equal"]) is bool
assert p["selected_78_is_nebe_sym2_family_full_character_equal"] is (
    p["selected_78_direct_sym2_full_character_pair_count"] == 2
    and p["selected_78_dual_sym2_full_character_pair_count"] == 2
)
assert p["common_729_necessary_equal_C3_phase_pair_count"] in (0, 1, 2)
assert type(p["suzuki_central_order_three_class_position"]) is int
assert p["suzuki_central_order_three_class_position"] > 0
if p["selected_78_is_nebe_sym2_family_full_character_equal"]:
    assert p["source_selected_c2_compatible_with_sym2_faithful12"] is True
    assert p["source_selected_degree_78_faithful_to_6Suz"] is False
assert type(p["source_selected_c2_compatible_with_sym2_faithful12"]) is bool
assert p["source_selected_c2_compatible_with_sym2_faithful12"] is (
    p["source_selected_S90_central_C2_trace"] == 66
)
if p["source_selected_degree_78_faithful_to_6Suz"]:
    assert p["source_selected_S90_central_C2_trace"] == -90

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
