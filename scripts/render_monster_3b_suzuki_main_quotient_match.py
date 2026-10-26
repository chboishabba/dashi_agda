#!/usr/bin/env python3
"""Validate and render the Monster 3B Suzuki/main quotient same-object receipt.

The GAP producer works entirely at character-table level and keeps two
order-three class coordinates distinct:

* the extraspecial central class is selected by ker(main -> 6.Suz.2);
* the diagonal class killed by qGtoN3B is selected by ker(main -> MN3B).

The full character matcher pays pair-family occurrence but deliberately does
not pay whether the diagonal kernel is <t1*t2> or <t1*t2^-1>, nor the resulting
individual a/b orientation inside the selected zeta sector.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path
from typing import Any


def req_int(p: dict[str, Any], key: str, *, positive: bool = True) -> int:
    value = p.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be an integer")
    if positive and value <= 0:
        raise ValueError(f"{key} must be positive")
    return value


def req_true(p: dict[str, Any], key: str) -> None:
    if p.get(key) is not True:
        raise ValueError(f"{key} must be true")


def req_false(p: dict[str, Any], key: str) -> None:
    if p.get(key) is not False:
        raise ValueError(f"{key} must be false")


def req_pair_int(p: dict[str, Any], key: str) -> list[int]:
    xs = p.get(key)
    if (
        not isinstance(xs, list)
        or len(xs) != 2
        or any(not isinstance(x, int) or isinstance(x, bool) or x <= 0 for x in xs)
        or len(set(xs)) != 2
    ):
        raise ValueError(f"{key} must be two distinct positive integers")
    return xs


def req_pair_label(p: dict[str, Any], key: str, degree: int) -> list[str]:
    xs = p.get(key)
    if (
        not isinstance(xs, list)
        or len(xs) != 2
        or any(not isinstance(x, str) or not x for x in xs)
        or len(set(xs)) != 2
    ):
        raise ValueError(f"{key} must be two distinct nonempty labels")
    if any(not x.startswith(str(degree)) for x in xs):
        raise ValueError(f"{key} labels do not have expected degree prefix {degree}")
    return xs


def validate(p: dict[str, Any]) -> dict[str, Any]:
    if p.get("main_table") != "3^1+12:6.Suz.2":
        raise ValueError("unexpected main table identity")
    if p.get("six_suz_table") != "6.Suz" or p.get("six_suz_outer_table") != "6.Suz.2":
        raise ValueError("unexpected Suzuki table identities")
    if p.get("mn3b_table") not in {"MN3B", "3^1+12.2.Suz.2"}:
        raise ValueError("unexpected MN3B table identity")

    versions = []
    for name in ("gap_runtime_version","ctbllib_runtime_version"):
        value = p.get(name)
        if not isinstance(value,str) or not value or any(ord(c)<32 for c in value):
            raise ValueError(name+" must be a nonempty source runtime version")
        versions.append(value)

    source_order = req_int(p, "six_suz_group_order")
    source_classes = req_int(p, "six_suz_class_count")
    if source_order != 2690072985600 or source_classes != 210:
        raise ValueError("source-selected 6.Suz table head does not match CTblLib/ATLAS")
    positions12 = req_pair_int(p, "six_suz_degree12_positions")
    positions78 = req_pair_int(p, "six_suz_degree78_positions")
    if set(positions12) & set(positions78):
        raise ValueError("selected 12/78 source Irr positions overlap")
    if any(i > source_classes for i in positions12+positions78):
        raise ValueError("selected Irr position exceeds source class count")

    base_pos = req_int(p, "base_1458_main_position")
    extraspecial_central_pos = req_int(
        p, "base_1458_extraspecial_central_class_position"
    )
    if req_int(p, "base_1458_central_trace", positive=False) != -729:
        raise ValueError("base 1458 central trace must be -729")
    req_true(p, "base_1458_outer_centre_inverting_trace_zero")
    q_kernel_pos = req_int(p, "qg_to_n3b_kernel_order_three_class_position")
    q_kernel_outer_pos = req_int(p, "qg_to_n3b_kernel_outer_class_position")
    if q_kernel_pos == extraspecial_central_pos:
        raise ValueError(
            "qGtoN3B diagonal kernel class must remain distinct from extraspecial central class"
        )

    labels12 = req_pair_label(p, "degree_12_atlas_labels", 12)
    labels78 = req_pair_label(p, "degree_78_atlas_labels", 78)
    outer12 = req_int(p, "outer_12_pair_position")
    outer78 = req_int(p, "outer_78_pair_position")
    split12 = req_pair_int(p, "main_12_split_positions")
    split78 = req_pair_int(p, "main_78_split_positions")
    down12 = req_int(p, "main_12_descending_position")
    down78 = req_int(p, "main_78_descending_position")
    if down12 not in split12 or down78 not in split78:
        raise ValueError("descending main position is not in its split pair")

    mn12 = req_int(p, "mn3b_12_position")
    mn78 = req_int(p, "mn3b_78_position")
    mult12 = req_int(p, "mn3b_12_monster_multiplicity")
    mult78 = req_int(p, "mn3b_78_monster_multiplicity")

    for key in (
        "extraspecial_centre_selected_by_outer_quotient_kernel",
        "qg_to_n3b_kernel_class_identified",
        "outer_pair_restriction_full_character_match",
        "main_product_split_full_character_decomposition",
        "quotient_descent_full_character_match",
        "restricted_monster_same_object_match",
    ):
        req_true(p, key)
    req_false(p, "diagonal_kernel_orientation_paid")
    req_false(p, "individual_zeta_label_orientation_paid")
    selected_faithful = p.get("source_selected_degree_78_faithful_to_6Suz")
    if type(selected_faithful) is not bool:
        raise ValueError("selected 78 faithfulness must be a bool from the matched source")
    c2_sym2_compatible = p.get("source_selected_c2_compatible_with_sym2_faithful12")
    if type(c2_sym2_compatible) is not bool:
        raise ValueError("source-selected Sym² C2 compatibility must be a bool")
    central3_pos = req_int(p, "suzuki_central_order_three_class_position")
    common729_pairs = req_int(
        p, "common_729_necessary_equal_C3_phase_pair_count", positive=False
    )
    if common729_pairs not in (0, 1, 2):
        raise ValueError("invalid equal-centre C3 pair count")
    full_direct = req_int(p, "selected_78_direct_sym2_full_character_pair_count", positive=False)
    full_dual = req_int(p, "selected_78_dual_sym2_full_character_pair_count", positive=False)
    full_nebe = p.get("selected_78_is_nebe_sym2_family_full_character_equal")
    if type(full_nebe) is not bool:
        raise ValueError("full 6.Suz Sym²12 selected-family equality must be bool")
    if full_direct not in (0,2) or full_dual not in (0,2):
        raise ValueError("selected conjugate78 Sym² family must match both or neither")
    if full_nebe != (full_direct == 2 and full_dual == 2):
        raise ValueError("full Sym² equality boolean disagrees with exact class functions")
    central2_pos = req_int(p, "suzuki_central_involution_class_position")
    source_trace = req_int(p, "source_selected_S90_central_C2_trace", positive=False)
    sym2_trace = req_int(p, "sym2_candidate_S90_central_C2_trace", positive=False)
    if source_trace not in (-90, 66) or sym2_trace != 66:
        raise ValueError("selected degree78 has invalid central C2 scalar")
    if c2_sym2_compatible != (source_trace == 66):
        raise ValueError("C2 Sym² compatibility must follow the selected C2 trace")
    if full_nebe and (not c2_sym2_compatible or selected_faithful):
        raise ValueError("selected Sym² is nonfaithful and must have central +66")
    if selected_faithful and source_trace != -90:
        raise ValueError("faithful degree78 cannot have positive C2 involution")

    # SAME-TABLE coordinates are not certified by a name, order, class
    # count, two centre positions and two Irr positions alone. Retain the
    # entire source-ordered conjugacy-class signature for the independent
    # all-conductor exporter to compare bytewise as integer arrays.
    def class_vector(key: str, *, zero_ok: bool = False) -> list[int]:
        xs = p.get(key)
        if (not isinstance(xs, list) or len(xs) != source_classes
                or any(type(x) is not int or x < (0 if zero_ok else 1) for x in xs)):
            raise ValueError(f"{key}: complete typed {source_classes}-class vector required")
        return xs

    class_orders = class_vector("six_suz_class_orders")
    class_sizes = class_vector("six_suz_class_sizes")
    square_map = class_vector("six_suz_power_map_2_zero_based", zero_ok=True)
    if (class_orders[0] != 1 or class_sizes[0] != 1
            or sum(class_sizes) != source_order or square_map[0] != 0):
        raise ValueError("source 6.Suz class identity/order/size/square-map inconsistency")
    if any(k >= source_classes for k in square_map):
        raise ValueError("source 6.Suz square map index outside table")
    for i, j in enumerate(square_map):
        if class_orders[j] != class_orders[i] // gcd(class_orders[i], 2):
            raise ValueError(f"source 6.Suz second-power map inconsistent at class {i+1}")
    c2 = central2_pos - 1
    c3 = central3_pos - 1
    if (c2 >= source_classes or c3 >= source_classes
            or class_orders[c2] != 2 or class_sizes[c2] != 1
            or square_map[c2] != 0 or class_orders[c3] != 3
            or class_sizes[c3] != 1 or square_map[c3] == c3
            or square_map[square_map[c3]] != c3):
        raise ValueError("source centre positions inconsistent with class signature")

    # Preserve the exact selected character rows, indexed by this GAP
    # table's literal classes. Metadata signatures alone can coincide under
    # noncentral class swaps. Actual cyclotomic equality is tested downstream
    # by the pre-existing exact all-conductor Cyc implementation.
    def source_rows(key: str) -> list[list[dict[str, Any]]]:
        xs = p.get(key)
        if not isinstance(xs, list) or len(xs) != 2:
            raise ValueError(f"{key}: exactly two selected character rows required")
        for row in xs:
            if not isinstance(row, list) or len(row) != source_classes:
                raise ValueError(f"{key}: incomplete 6.Suz full-class row")
            for cell in row:
                if not isinstance(cell, dict):
                    raise ValueError(f"{key}: malformed cyclotomic cell")
                n = cell.get("conductor")
                coeff = cell.get("coefficients")
                if (type(n) is not int or not 1 <= n <= 4096
                        or not isinstance(coeff, list) or len(coeff) != n
                        or any(type(v) is not str for v in coeff)):
                    raise ValueError(f"{key}: invalid exact cyclotomic source record")
        return xs

    selected12rows = source_rows("six_suz_selected_12_all_class_values")
    selected78rows = source_rows("six_suz_selected_78_all_class_values")

    return {
        "class_orders": class_orders,
        "selected12rows": selected12rows,
        "selected78rows": selected78rows,
        "class_sizes": class_sizes,
        "power_map_2_zero_based": square_map,
        "base_pos": base_pos,
        "extraspecial_central_pos": extraspecial_central_pos,
        "q_kernel_pos": q_kernel_pos,
        "q_kernel_outer_pos": q_kernel_outer_pos,
        "labels12": labels12,
        "labels78": labels78,
        "gap_version": versions[0],
        "ctbllib_version": versions[1],
        "source_order": source_order,
        "source_classes": source_classes,
        "positions12": positions12,
        "positions78": positions78,
        "outer12": outer12,
        "outer78": outer78,
        "split12": split12,
        "split78": split78,
        "down12": down12,
        "down78": down78,
        "mn12": mn12,
        "mn78": mn78,
        "mult12": mult12,
        "mult78": mult78,
        "central2_pos": central2_pos,
        "central3_pos": central3_pos,
        "common729_pairs": common729_pairs,
        "full_direct": full_direct,
        "full_dual": full_dual,
        "full_nebe": full_nebe,
        "source_trace": source_trace,
        "sym2_trace": sym2_trace,
        "selected_faithful": selected_faithful,
        "c2_sym2_compatible": c2_sym2_compatible,
    }


def agda_string(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def agda_pair_nat(xs: list[int]) -> str:
    return f"{xs[0]} ∷ {xs[1]} ∷ []"


def agda_pair_string(xs: list[str]) -> str:
    return f'"{agda_string(xs[0])}" ∷ "{agda_string(xs[1])}" ∷ []'


def render(v: dict[str, Any], digest: str) -> str:
    return f'''module DASHI.Moonshine.Generated.Monster3BSuzukiMainQuotientMatchCertificate where

-- GENERATED CERTIFICATE.
-- Full character-table matching pays the 12a/b and 78a/b PAIR-FAMILY
-- occurrence in the actual restricted Monster character.  The extraspecial
-- central class and qGtoN3B diagonal-kernel class remain separately identified.
-- Diagonal t1*t2 versus t1*t2^-1 orientation and individual a/b orientation
-- remain unpaid.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

inputSHA256 : String
inputSHA256 = "{digest}"

base1458MainPosition : Nat
base1458MainPosition = {v['base_pos']}
extraspecialCentralClassPosition : Nat
extraspecialCentralClassPosition = {v['extraspecial_central_pos']}
base1458ExtraspecialCentralTraceMagnitude : Nat
base1458ExtraspecialCentralTraceMagnitude = 729
qGtoN3BKernelOrderThreeClassPosition : Nat
qGtoN3BKernelOrderThreeClassPosition = {v['q_kernel_pos']}
qGtoN3BKernelOuterClassPosition : Nat
qGtoN3BKernelOuterClassPosition = {v['q_kernel_outer_pos']}

sixSuzDegree12AtlasLabels : List String
sixSuzDegree12AtlasLabels = {agda_pair_string(v['labels12'])}
sixSuzDegree78AtlasLabels : List String
sixSuzDegree78AtlasLabels = {agda_pair_string(v['labels78'])}
source6SuzGroupOrder : Nat
source6SuzGroupOrder = {v['source_order']}
source6SuzClassCount : Nat
source6SuzClassCount = {v['source_classes']}
source6SuzDegree12IrrPositions : List Nat
source6SuzDegree12IrrPositions = {agda_pair_nat(v['positions12'])}
source6SuzDegree78IrrPositions : List Nat
source6SuzDegree78IrrPositions = {agda_pair_nat(v['positions78'])}

-- Chosen source 78 family is selected by full class-function restriction,
-- main quotient descent and actual Monster occurrence, NOT by a
-- presupposed faithful 6.Suz character filter.
sixSuzCentralInvolutionClassPosition : Nat
sixSuzCentralInvolutionClassPosition = {v['central2_pos']}
sixSuzCentralOrderThreeClassPosition : Nat
sixSuzCentralOrderThreeClassPosition = {v['central3_pos']}
common729NecessaryEqualC3PhasePairCount : Nat
common729NecessaryEqualC3PhasePairCount = {v['common729_pairs']}
selected78DirectSym2FullClassCharacterMatchCount : Nat
selected78DirectSym2FullClassCharacterMatchCount = {v['full_direct']}
selected78DualSym2FullClassCharacterMatchCount : Nat
selected78DualSym2FullClassCharacterMatchCount = {v['full_dual']}
selected78NebeSym2FullClassCharacterEqual : Bool
selected78NebeSym2FullClassCharacterEqual = {str(v['full_nebe']).lower()}
selectedDegree78FaithfulToSixSuz : Bool
selectedDegree78FaithfulToSixSuz = {str(v['selected_faithful']).lower()}
selectedC2SymSquareNecessaryCompatibility : Bool
selectedC2SymSquareNecessaryCompatibility = {str(v['c2_sym2_compatible']).lower()}
selectedMultiplicityCentralC2TraceMagnitude : Nat
selectedMultiplicityCentralC2TraceMagnitude = {abs(v['source_trace'])}
selectedMultiplicityCentralC2TraceNegative : Bool
selectedMultiplicityCentralC2TraceNegative = {str(v['source_trace'] < 0).lower()}
candidateSymSquareCentralC2PositiveMagnitude : Nat
candidateSymSquareCentralC2PositiveMagnitude = {v['sym2_trace']}

outer12PairPosition : Nat
outer12PairPosition = {v['outer12']}
outer78PairPosition : Nat
outer78PairPosition = {v['outer78']}
main12SplitPositions : List Nat
main12SplitPositions = {agda_pair_nat(v['split12'])}
main78SplitPositions : List Nat
main78SplitPositions = {agda_pair_nat(v['split78'])}
main12DescendingPosition : Nat
main12DescendingPosition = {v['down12']}
main78DescendingPosition : Nat
main78DescendingPosition = {v['down78']}
mn3b12Position : Nat
mn3b12Position = {v['mn12']}
mn3b78Position : Nat
mn3b78Position = {v['mn78']}
mn3b12MonsterMultiplicity : Nat
mn3b12MonsterMultiplicity = {v['mult12']}
mn3b78MonsterMultiplicity : Nat
mn3b78MonsterMultiplicity = {v['mult78']}

extraspecialCentreSelectedByOuterQuotientKernel : Bool
extraspecialCentreSelectedByOuterQuotientKernel = true
qGtoN3BKernelClassIdentified : Bool
qGtoN3BKernelClassIdentified = true
outerPairRestrictionFullCharacterMatch : Bool
outerPairRestrictionFullCharacterMatch = true
mainProductSplitFullCharacterDecomposition : Bool
mainProductSplitFullCharacterDecomposition = true
quotientDescentFullCharacterMatch : Bool
quotientDescentFullCharacterMatch = true
restrictedMonsterSameObjectMatch : Bool
restrictedMonsterSameObjectMatch = true
pairFamilyMonsterOccurrencePaid : Bool
pairFamilyMonsterOccurrencePaid = true
diagonalKernelOrientationPaid : Bool
diagonalKernelOrientationPaid = false
individualZetaLabelOrientationPaid : Bool
individualZetaLabelOrientationPaid = false

baseFusionDegree : 2 * 729 ≡ 1458
baseFusionDegree = refl
twelvePairProductDegree : 1458 * 24 ≡ 2 * 17496
twelvePairProductDegree = refl
seventyEightPairProductDegree : 1458 * 156 ≡ 2 * 113724
seventyEightPairProductDegree = refl
selectedPhaseDimension : 729 * (12 + 78) ≡ 65610
selectedPhaseDimension = refl
'''


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path)
    ap.add_argument("output", type=Path)
    args = ap.parse_args()
    raw = args.input.read_bytes()
    payload = json.loads(raw)
    values = validate(payload)
    digest = hashlib.sha256(raw).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(values, digest), encoding="utf-8")
    print(
        "validated Suzuki/main/N3B/Monster pair-family same-object match; "
        f"12={values['labels12']} 78={values['labels78']} "
        f"qkernel={values['q_kernel_pos']} sha256={digest}"
    )


if __name__ == "__main__":
    main()
