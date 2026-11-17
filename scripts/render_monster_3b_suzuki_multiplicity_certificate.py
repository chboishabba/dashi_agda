#!/usr/bin/env python3
"""Validate the source-native 6.Suz multiplicity-character candidate receipt.

The generated Agda file pins exact CTblLib character positions, ATLAS semantic
labels, and central phase orientation.  It does not claim which candidate occurs
in the Monster restriction; that same-object match remains a separate theorem /
execution receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


def _positions(payload: dict[str, Any], key: str, min_count: int = 2) -> list[int]:
    xs = payload.get(key)
    if (
        not isinstance(xs, list)
        or len(xs) < min_count
        or any(not isinstance(x, int) or isinstance(x, bool) or x <= 0 for x in xs)
        or len(set(xs)) != len(xs)
    ):
        raise ValueError(f"{key} must be >= {min_count} distinct positive integer positions")
    return xs


def _labels(payload: dict[str, Any], key: str, min_count: int = 2) -> list[str]:
    xs = payload.get(key)
    if (
        not isinstance(xs, list)
        or len(xs) < min_count
        or any(not isinstance(x, str) or not x.strip() for x in xs)
        or len(set(xs)) != len(xs)
    ):
        raise ValueError(f"{key} must be >= {min_count} distinct nonempty ATLAS labels")
    return xs


def _rows(
    payload: dict[str, Any],
    key: str,
    degree: int,
    positions: list[int],
    labels: list[str],
) -> list[dict[str, Any]]:
    rows = payload.get(key)
    if not isinstance(rows, list) or len(rows) != len(positions):
        raise ValueError(f"{key} must have one candidate row per source position")
    seen_positions: list[int] = []
    seen_labels: list[str] = []
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError(f"{key} row must be an object")
        pos = row.get("position")
        label = row.get("atlas_label")
        if pos not in positions or label not in labels or row.get("degree") != degree:
            raise ValueError(f"{key} row has unexpected position/label/degree")
        p1 = row.get("first_central_phase")
        p2 = row.get("second_central_phase")
        if {p1, p2} != {"zeta", "zetaSquared"} and not (p1 == p2 == "trivial"):
            raise ValueError(f"{key} C3 phases must be inverse nontrivial or both trivial")
        if degree == 12 and (p1 == "trivial" or p2 == "trivial"):
            raise ValueError("faithful degree12 cannot have trivial C3 phase")
        faithful = row.get("faithful_to_6Suz")
        if type(faithful) is not bool:
            raise ValueError(f"{key} must report a boolean faithfulness-to-6.Suz status")
        if degree == 12 and faithful is not True:
            raise ValueError("degree-12 candidate must be faithful to 6.Suz")
        seen_positions.append(pos)
        seen_labels.append(label)
    if sorted(seen_positions) != sorted(positions):
        raise ValueError(f"{key} positions do not match candidate list")
    if sorted(seen_labels) != sorted(labels):
        raise ValueError(f"{key} labels do not match candidate label list")
    return rows


def validate(payload: dict[str, Any]) -> dict[str, Any]:
    if payload.get("table") != "6.Suz" or payload.get("outer_table") != "6.Suz.2":
        raise ValueError("unexpected Suzuki table identities")
    if payload.get("label_source") != "CTblLib AtlasLabelsOfIrreducibles(short)":
        raise ValueError("unexpected ATLAS-label source")
    if payload.get("source_native_729_tensor_factorisation") is not True:
        raise ValueError("source_native_729_tensor_factorisation must be true")
    if payload.get("atlas_label_position_alignment_paid") is not True:
        raise ValueError("atlas_label_position_alignment_paid must be true")
    if payload.get("monster_same_object_match_paid") is not False:
        raise ValueError("candidate receipt must not pre-pay the Monster same-object match")

    central = payload.get("central_order_three_classes")
    if (
        not isinstance(central, list)
        or len(central) != 2
        or any(not isinstance(x, int) or isinstance(x, bool) or x <= 0 for x in central)
        or central[0] == central[1]
    ):
        raise ValueError("expected two distinct positive central order-three class positions")

    p12 = _positions(payload, "faithful_degree_12_positions")
    if payload.get("degree_78_family_filter") != "all_character_degrees_no_faithfulness_filter":
        raise ValueError("degree78 inventory must contain ALL candidates, not an assumed source family")
    p78 = _positions(payload, "degree_78_positions")
    all78 = payload.get("all_degree_78_positions")
    faithful78 = payload.get("faithful_degree_78_positions")
    more78 = payload.get("nonfaithful_degree_78_positions")
    if any(not isinstance(xs, list) or any(type(i) is not int or i <= 0 for i in xs)
           or len(set(xs)) != len(xs)
           for xs in (all78, faithful78, more78)):
        raise ValueError("invalid faithful/nonfaithful inventory types or duplicates")
    if set(all78) != set(p78) or set(p78) != (set(faithful78) | set(more78)):
        raise ValueError("all degree78 positions must partition into faithful/nonfaithful")
    if set(faithful78) & set(more78):
        raise ValueError("faithful/nonfaithful 78 overlap")
    l12 = _labels(payload, "faithful_degree_12_atlas_labels")
    l78 = _labels(payload, "degree_78_atlas_labels")
    r12 = _rows(payload, "degree_12_rows", 12, p12, l12)
    r78 = _rows(payload, "degree_78_rows", 78, p78, l78)
    if {row["position"] for row in r78 if row["faithful_to_6Suz"]} != set(faithful78):
        raise ValueError("faithful degree78 row flags inconsistent with partition")

    fusion_length = payload.get("fusion_length")
    if not isinstance(fusion_length, int) or isinstance(fusion_length, bool) or fusion_length <= 0:
        raise ValueError("fusion_length must be positive")

    return {
        "central": central,
        "p12": p12,
        "p78": p78,
        "l12": l12,
        "l78": l78,
        "r12": r12,
        "r78": r78,
        "nonfaithful78": more78,
        "faithful78": faithful78,
        "all78": all78,
        "fusion_length": fusion_length,
    }


def nat_list(xs: list[int]) -> str:
    return " ∷ ".join(str(x) for x in xs) + " ∷ []"


def string_list(xs: list[str]) -> str:
    escaped = [x.replace("\\", "\\\\").replace('"', '\\"') for x in xs]
    return " ∷ ".join(f'"{x}"' for x in escaped) + " ∷ []"


def agda(v: dict[str, Any], digest: str) -> str:
    return f'''module DASHI.Moonshine.Generated.Monster3BSuzukiMultiplicityCharacterCertificate where

-- GENERATED FROM CTblLib 6.Suz / 6.Suz.2 TABLE DATA.
-- Candidate character positions, ATLAS labels and phase orientation are
-- certified here.  Same-object occurrence in the Monster restriction is
-- deliberately NOT paid.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

inputSHA256 : String
inputSHA256 = "{digest}"

atlasLabelSource : String
atlasLabelSource = "CTblLib AtlasLabelsOfIrreducibles(short)"

firstCentralOrderThreeClass : Nat
firstCentralOrderThreeClass = {v['central'][0]}
secondCentralOrderThreeClass : Nat
secondCentralOrderThreeClass = {v['central'][1]}

faithfulDegree12Positions : List Nat
faithfulDegree12Positions = {nat_list(v['p12'])}
degree78Positions : List Nat
degree78Positions = {nat_list(v['p78'])}

faithfulDegree12AtlasLabels : List String
faithfulDegree12AtlasLabels = {string_list(v['l12'])}
degree78AtlasLabels : List String
degree78AtlasLabels = {string_list(v['l78'])}

-- All source candidate degrees78; actual Monster selection is deferred
-- to the independent main -> MN3B -> Monster FULL character matcher.
selectedMonsterDegree78CharacterIdentifiedHere : Bool
selectedMonsterDegree78CharacterIdentifiedHere = false
faithfulDegree78Positions : List Nat
faithfulDegree78Positions = {nat_list(v['faithful78']) if v['faithful78'] else '[]'}
nonfaithfulDegree78Positions : List Nat
nonfaithfulDegree78Positions = {nat_list(v['nonfaithful78'])}
completeDegree78Inventory : List Nat
completeDegree78Inventory = {nat_list(v['all78'])}
actualMonsterDegree78FamilySelectedByThisInventory : Bool
actualMonsterDegree78FamilySelectedByThisInventory = false

sixSuzToOuterFusionLength : Nat
sixSuzToOuterFusionLength = {v['fusion_length']}

sourceNativeTensorFactorisationObserved : Bool
sourceNativeTensorFactorisationObserved = true
atlasLabelPositionAlignmentPaid : Bool
atlasLabelPositionAlignmentPaid = true
monsterSameObjectMatchPaid : Bool
monsterSameObjectMatchPaid = false

multiplicityDegreeSum : 12 + 78 ≡ 90
multiplicityDegreeSum = refl
selectedPhaseDegree : 729 * (12 + 78) ≡ 65610
selectedPhaseDegree = refl
pairedOuterDegree : 2 * (729 * (12 + 78)) ≡ 131220
pairedOuterDegree = refl
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
    args.output.write_text(agda(values, digest), encoding="utf-8")
    print(
        "validated 6.Suz multiplicity candidates "
        f"labels12={values['l12']} labels78={values['l78']} sha256={digest}"
    )


if __name__ == "__main__":
    main()
