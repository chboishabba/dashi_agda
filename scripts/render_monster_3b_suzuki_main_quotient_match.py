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

    base_pos = req_int(p, "base_1458_main_position")
    extraspecial_central_pos = req_int(
        p, "base_1458_extraspecial_central_class_position"
    )
    if req_int(p, "base_1458_central_trace", positive=False) != -729:
        raise ValueError("base 1458 central trace must be -729")
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

    return {
        "base_pos": base_pos,
        "extraspecial_central_pos": extraspecial_central_pos,
        "q_kernel_pos": q_kernel_pos,
        "q_kernel_outer_pos": q_kernel_outer_pos,
        "labels12": labels12,
        "labels78": labels78,
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
