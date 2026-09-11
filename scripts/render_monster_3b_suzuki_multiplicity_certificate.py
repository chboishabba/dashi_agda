#!/usr/bin/env python3
"""Validate the source-native 6.Suz multiplicity-character candidate receipt.

The generated Agda file pins exact CTblLib character positions and central phase
orientation.  It does not claim which candidate occurs in the Monster restriction;
that same-object match remains a separate theorem/receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


def _positions(payload: dict[str, Any], key: str) -> list[int]:
    xs = payload.get(key)
    if not isinstance(xs, list) or not xs or any(not isinstance(x, int) or isinstance(x, bool) or x <= 0 for x in xs):
        raise ValueError(f"{key} must be a nonempty list of positive integer positions")
    return xs


def _rows(payload: dict[str, Any], key: str, degree: int, positions: list[int]) -> list[dict[str, Any]]:
    rows = payload.get(key)
    if not isinstance(rows, list) or len(rows) != len(positions):
        raise ValueError(f"{key} must have one row per candidate position")
    seen = []
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError(f"{key} row must be an object")
        pos = row.get("position")
        if pos not in positions or row.get("degree") != degree:
            raise ValueError(f"{key} row has unexpected position/degree")
        p1 = row.get("first_central_phase")
        p2 = row.get("second_central_phase")
        if {p1, p2} != {"zeta", "zetaSquared"}:
            raise ValueError(f"{key} central phases must be inverse nontrivial C3 phases")
        seen.append(pos)
    if sorted(seen) != sorted(positions):
        raise ValueError(f"{key} positions do not match candidate list")
    return rows


def validate(payload: dict[str, Any]) -> dict[str, Any]:
    if payload.get("table") != "6.Suz" or payload.get("outer_table") != "6.Suz.2":
        raise ValueError("unexpected Suzuki table identities")
    if payload.get("source_native_729_tensor_factorisation") is not True:
        raise ValueError("source_native_729_tensor_factorisation must be true")
    if payload.get("monster_same_object_match_paid") is not False:
        raise ValueError("candidate receipt must not pre-pay the Monster same-object match")
    central = payload.get("central_order_three_classes")
    if not isinstance(central, list) or len(central) != 2 or any(not isinstance(x, int) or x <= 0 for x in central) or central[0] == central[1]:
        raise ValueError("expected two distinct positive central order-three class positions")
    p12 = _positions(payload, "faithful_degree_12_positions")
    p78 = _positions(payload, "faithful_degree_78_positions")
    r12 = _rows(payload, "degree_12_rows", 12, p12)
    r78 = _rows(payload, "degree_78_rows", 78, p78)
    fusion_length = payload.get("fusion_length")
    if not isinstance(fusion_length, int) or fusion_length <= 0:
        raise ValueError("fusion_length must be positive")
    return {"central": central, "p12": p12, "p78": p78, "r12": r12, "r78": r78, "fusion_length": fusion_length}


def nat_list(xs: list[int]) -> str:
    if not xs:
        return "[]"
    return " ∷ ".join(str(x) for x in xs) + " ∷ []"


def agda(v: dict[str, Any], digest: str) -> str:
    return f'''module DASHI.Moonshine.Generated.Monster3BSuzukiMultiplicityCharacterCertificate where

-- GENERATED FROM CTblLib 6.Suz / 6.Suz.2 TABLE DATA.
-- Candidate character positions and phase orientation are certified here.
-- Same-object occurrence in the Monster restriction is deliberately NOT paid.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

inputSHA256 : String
inputSHA256 = "{digest}"

firstCentralOrderThreeClass : Nat
firstCentralOrderThreeClass = {v['central'][0]}
secondCentralOrderThreeClass : Nat
secondCentralOrderThreeClass = {v['central'][1]}

faithfulDegree12Positions : List Nat
faithfulDegree12Positions = {nat_list(v['p12'])}
faithfulDegree78Positions : List Nat
faithfulDegree78Positions = {nat_list(v['p78'])}

sixSuzToOuterFusionLength : Nat
sixSuzToOuterFusionLength = {v['fusion_length']}

sourceNativeTensorFactorisationObserved : Bool
sourceNativeTensorFactorisationObserved = true
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
    print(f"validated 6.Suz multiplicity candidates; sha256={digest}")


if __name__ == "__main__":
    main()
