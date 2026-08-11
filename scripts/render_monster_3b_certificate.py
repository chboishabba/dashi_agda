#!/usr/bin/env python3
"""Render a fail-closed Agda certificate from the GAP/CTblLib MN3B result.

The GAP producer proves classwise reconstruction against the stored MN3B -> M
fusion before writing JSON.  This renderer independently validates the numeric
schema, total contribution, 3B trace and eigenspace multiplicities, then emits
an Agda module whose arithmetic consequences are kernel checked.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

EXPECTED_DEGREE = 196883
EXPECTED_TRACE = 53
EXPECTED_INVARIANT = 65663
EXPECTED_NONTRIVIAL = 65610


def require_int(payload: dict[str, Any], key: str) -> int:
    value = payload.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be an integer")
    return value


def validate(payload: dict[str, Any]) -> dict[str, int]:
    if payload.get("classwise_reconstruction") is not True:
        raise ValueError("GAP did not certify classwise reconstruction")

    degree = require_int(payload, "monster_character_degree")
    reconstructed = require_int(payload, "reconstructed_degree")
    trace = require_int(payload, "three_b_trace")
    invariant = require_int(payload, "invariant_multiplicity")
    zeta = require_int(payload, "zeta_multiplicity")
    zeta2 = require_int(payload, "zeta_squared_multiplicity")
    central_class = require_int(payload, "mn3b_central_3b_class_position")
    central_size = require_int(payload, "mn3b_central_3b_class_size")

    if degree != EXPECTED_DEGREE or reconstructed != EXPECTED_DEGREE:
        raise ValueError("unexpected Monster degree")
    if trace != EXPECTED_TRACE:
        raise ValueError("unexpected 3B trace")
    if (invariant, zeta, zeta2) != (
        EXPECTED_INVARIANT,
        EXPECTED_NONTRIVIAL,
        EXPECTED_NONTRIVIAL,
    ):
        raise ValueError("unexpected 3B eigenspace multiplicities")
    if invariant + zeta + zeta2 != degree:
        raise ValueError("3B eigenspaces do not reconstruct the degree")
    if zeta + trace != invariant:
        raise ValueError("3B trace is not the invariant excess")
    if central_size != 2:
        raise ValueError("the selected central 3B class must have size two")

    constituents = payload.get("constituents")
    if not isinstance(constituents, list) or not constituents:
        raise ValueError("constituents must be a nonempty list")

    contribution_sum = 0
    weighted_checksum = 0
    for row in constituents:
        if not isinstance(row, dict):
            raise ValueError("constituent row must be an object")
        position = require_int(row, "position")
        multiplicity = require_int(row, "multiplicity")
        constituent_degree = require_int(row, "degree")
        contribution = require_int(row, "contribution")
        if position <= 0 or multiplicity <= 0 or constituent_degree <= 0:
            raise ValueError("constituent data must be positive")
        if multiplicity * constituent_degree != contribution:
            raise ValueError("constituent contribution mismatch")
        contribution_sum += contribution
        weighted_checksum += position * contribution

    if contribution_sum != degree:
        raise ValueError("constituent contributions do not reconstruct degree")

    return {
        "degree": degree,
        "trace": trace,
        "invariant": invariant,
        "zeta": zeta,
        "zeta2": zeta2,
        "central_class": central_class,
        "central_size": central_size,
        "constituent_count": len(constituents),
        "contribution_sum": contribution_sum,
        "weighted_checksum": weighted_checksum,
        "source_class_count": require_int(payload, "source_class_count"),
    }


def agda_module(values: dict[str, int], payload: dict[str, Any]) -> str:
    source = str(payload.get("source_table", "M")).replace('"', "")
    target = str(payload.get("target_table", "MN3B")).replace('"', "")
    return f'''module DASHI.Moonshine.Generated.Monster3BRestrictionCertificate where

-- GENERATED FILE.  Source: GAP + CTblLib stored class fusion.
-- The producer checked nonnegative integral multiplicities and equality on
-- every MN3B conjugacy-class value before emitting the JSON consumed here.

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

sourceTable : String
sourceTable = "{source}"

targetTable : String
targetTable = "{target}"

monsterCharacterDegree : Nat
monsterCharacterDegree = {values['degree']}

threeBTrace : Nat
threeBTrace = {values['trace']}

invariantMultiplicity : Nat
invariantMultiplicity = {values['invariant']}

zetaMultiplicity : Nat
zetaMultiplicity = {values['zeta']}

zetaSquaredMultiplicity : Nat
zetaSquaredMultiplicity = {values['zeta2']}

centralThreeBClassPosition : Nat
centralThreeBClassPosition = {values['central_class']}

centralThreeBClassSize : Nat
centralThreeBClassSize = {values['central_size']}

sourceClassCount : Nat
sourceClassCount = {values['source_class_count']}

constituentCount : Nat
constituentCount = {values['constituent_count']}

constituentContributionSum : Nat
constituentContributionSum = {values['contribution_sum']}

constituentWeightedChecksum : Nat
constituentWeightedChecksum = {values['weighted_checksum']}

classwiseReconstructionCertified : Bool
classwiseReconstructionCertified = true

phaseDimensionCertificate :
  invariantMultiplicity + zetaMultiplicity + zetaSquaredMultiplicity
  ≡ monsterCharacterDegree
phaseDimensionCertificate = refl

traceAsInvariantExcessCertificate :
  zetaMultiplicity + threeBTrace ≡ invariantMultiplicity
traceAsInvariantExcessCertificate = refl

regularResidualDimensionCertificate :
  3 * zetaMultiplicity + threeBTrace ≡ monsterCharacterDegree
regularResidualDimensionCertificate = refl

contributionCertificate :
  constituentContributionSum ≡ monsterCharacterDegree
contributionCertificate = refl

centralClassSizeCertificate : centralThreeBClassSize ≡ 2
centralClassSizeCertificate = refl
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    payload = json.loads(args.input.read_text())
    values = validate(payload)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(agda_module(values, payload))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
