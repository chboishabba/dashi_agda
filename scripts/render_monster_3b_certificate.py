#!/usr/bin/env python3
"""Validate the actual MN3B restriction and render an Agda certificate.

The GAP producer checks the stored MN3B -> Monster fusion, reconstructs the
196883-character classwise, identifies the normal extraspecial kernel carrier,
and partitions every nonzero constituent by its value on the size-two central
3B orbit:

* centre-trivial: chi(z) = chi(1);
* paired phases: 2 chi(z) = -chi(1).

Every paired-phase degree must be divisible by 2*729.  After constituent
multiplicities are expanded, the quotient degrees must be exactly [12, 78].
This is an actual normalizer-level multiplicity-degree split.  It does not
split the zeta and zeta^2 sectors into explicit matrices, compute their full
inertia characters, or construct an intertwiner.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

EXPECTED_DEGREE = 196_883
EXPECTED_TRACE = 53
EXPECTED_INVARIANT = 65_663
EXPECTED_NONTRIVIAL = 65_610
EXPECTED_KERNEL_ORDER = 3**13
EXPECTED_PHASE_PAIR_TOTAL = 2 * EXPECTED_NONTRIVIAL
EXPECTED_PAIR_DEGREE = 2 * 729
EXPECTED_MULTIPLICITY_DEGREES = [12, 78]
EXPECTED_CONSTITUENT_DEGREES = [
    EXPECTED_PAIR_DEGREE * degree for degree in EXPECTED_MULTIPLICITY_DEGREES
]


def require_int(mapping: dict[str, Any], key: str) -> int:
    value = mapping.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be an integer")
    return value


def require_true(mapping: dict[str, Any], key: str) -> None:
    if mapping.get(key) is not True:
        raise ValueError(f"{key} must be true")


def require_int_list(mapping: dict[str, Any], key: str) -> list[int]:
    value = mapping.get(key)
    if not isinstance(value, list) or any(
        not isinstance(item, int) or isinstance(item, bool) for item in value
    ):
        raise ValueError(f"{key} must be a list of integers")
    return value


def validate_phase_split(payload: dict[str, Any], central_class: int) -> dict[str, int]:
    centre_total = require_int(payload, "centre_trivial_constituent_degree_total")
    pair_total = require_int(payload, "phase_pair_constituent_degree_total")
    pair_degree = require_int(payload, "phase_pair_heisenberg_degree")
    multiplicity_degrees = require_int_list(
        payload, "phase_pair_multiplicity_degrees"
    )
    require_true(payload, "twelve_plus_seventy_eight_degree_split_certified")

    if centre_total != EXPECTED_INVARIANT:
        raise ValueError("centre-trivial degree total is not 65663")
    if pair_total != EXPECTED_PHASE_PAIR_TOTAL:
        raise ValueError("paired-phase degree total is not 131220")
    if pair_degree != EXPECTED_PAIR_DEGREE:
        raise ValueError("paired Heisenberg degree is not 1458")
    if multiplicity_degrees != EXPECTED_MULTIPLICITY_DEGREES:
        raise ValueError("multiplicity-degree split is not [12, 78]")
    if pair_degree * sum(multiplicity_degrees) != pair_total:
        raise ValueError("paired-phase tensor reconstruction failed")

    constituents = payload.get("constituents")
    if not isinstance(constituents, list) or not constituents:
        raise ValueError("constituents must be a nonempty list")

    positions: list[int] = []
    paired_positions: list[int] = []
    contribution_sum = 0
    weighted_checksum = 0
    centre_row_total = 0
    pair_row_total = 0

    for row in constituents:
        if not isinstance(row, dict):
            raise ValueError("constituent row must be an object")
        position = require_int(row, "position")
        multiplicity = require_int(row, "multiplicity")
        degree = require_int(row, "degree")
        central_trace = require_int(row, "central_trace")
        contribution = require_int(row, "contribution")
        kind = row.get("clifford_type")

        if position <= 0 or multiplicity <= 0 or degree <= 0:
            raise ValueError("constituent data must be positive")
        if contribution != multiplicity * degree:
            raise ValueError("constituent contribution mismatch")
        if kind == "centre-trivial":
            if central_trace != degree:
                raise ValueError("centre-trivial central trace ratio failed")
            centre_row_total += contribution
        elif kind == "paired-phase":
            if 2 * central_trace != -degree:
                raise ValueError("paired-phase central trace ratio failed")
            if degree % pair_degree != 0:
                raise ValueError("paired-phase degree is not divisible by 1458")
            pair_row_total += contribution
            paired_positions.append(position)
        else:
            raise ValueError("unknown Clifford constituent type")

        positions.append(position)
        contribution_sum += contribution
        weighted_checksum += position * contribution

    if len(set(positions)) != len(positions):
        raise ValueError("constituent positions must be unique")
    if contribution_sum != EXPECTED_DEGREE:
        raise ValueError("constituent contributions do not reconstruct 196883")
    if centre_row_total != centre_total or pair_row_total != pair_total:
        raise ValueError("Clifford row totals disagree with declared totals")

    pair_rows = payload.get("phase_pair_constituents")
    if not isinstance(pair_rows, list) or not pair_rows:
        raise ValueError("phase_pair_constituents must be a nonempty list")

    pair_positions: list[int] = []
    expanded_degrees: list[int] = []
    pair_contribution_sum = 0
    pair_checksum = 0

    for row in pair_rows:
        if not isinstance(row, dict):
            raise ValueError("phase-pair row must be an object")
        position = require_int(row, "position")
        multiplicity = require_int(row, "multiplicity")
        degree = require_int(row, "degree")
        central_trace = require_int(row, "central_trace")
        multiplicity_degree = require_int(row, "multiplicity_degree")
        contribution = require_int(row, "contribution")

        if position <= 0 or multiplicity <= 0 or multiplicity_degree <= 0:
            raise ValueError("phase-pair row data must be positive")
        if 2 * central_trace != -degree:
            raise ValueError("phase-pair trace ratio failed")
        if degree != pair_degree * multiplicity_degree:
            raise ValueError("phase-pair degree is not 1458 times its quotient")
        if contribution != multiplicity * degree:
            raise ValueError("phase-pair contribution mismatch")

        pair_positions.append(position)
        pair_contribution_sum += contribution
        pair_checksum += position * contribution
        expanded_degrees.extend([multiplicity_degree] * multiplicity)

    if pair_positions != paired_positions:
        raise ValueError("phase-pair rows disagree with all constituent rows")
    if pair_contribution_sum != pair_total:
        raise ValueError("phase-pair rows do not reconstruct 131220")
    if sorted(expanded_degrees) != EXPECTED_MULTIPLICITY_DEGREES:
        raise ValueError("expanded multiplicity degrees are not [12, 78]")

    actual_constituent_degrees = sorted(pair_degree * value for value in expanded_degrees)
    if actual_constituent_degrees != EXPECTED_CONSTITUENT_DEGREES:
        raise ValueError("paired constituent degrees are not 17496 and 113724")

    return {
        "constituent_count": len(constituents),
        "contribution_sum": contribution_sum,
        "weighted_checksum": weighted_checksum,
        "centre_total": centre_total,
        "pair_total": pair_total,
        "pair_degree": pair_degree,
        "first_multiplicity_degree": multiplicity_degrees[0],
        "second_multiplicity_degree": multiplicity_degrees[1],
        "first_constituent_degree": actual_constituent_degrees[0],
        "second_constituent_degree": actual_constituent_degrees[1],
        "pair_constituent_count": len(pair_rows),
        "pair_checksum": pair_checksum,
        "central_class": central_class,
    }


def validate_kernel(payload: dict[str, Any], degree: int, trace: int, central_class: int) -> dict[str, int]:
    kernel_order = require_int(payload, "extraspecial_kernel_order")
    class_count = require_int(payload, "extraspecial_kernel_class_count")
    class_size_sum = require_int(payload, "extraspecial_kernel_class_size_sum")
    invariant_numerator = require_int(
        payload, "extraspecial_kernel_invariant_numerator"
    )
    invariant_dimension = require_int(
        payload, "extraspecial_kernel_invariant_dimension"
    )
    require_true(payload, "extraspecial_kernel_contains_central_3b")
    require_true(payload, "extraspecial_kernel_all_nonidentity_orders_three")

    if kernel_order != EXPECTED_KERNEL_ORDER or class_size_sum != kernel_order:
        raise ValueError("extraspecial kernel order/class-size sum failed")
    if invariant_dimension < 0:
        raise ValueError("extraspecial kernel invariant dimension is negative")
    if invariant_numerator != kernel_order * invariant_dimension:
        raise ValueError("extraspecial kernel averaging identity failed")

    positions = require_int_list(payload, "extraspecial_kernel_class_positions")
    rows = payload.get("extraspecial_kernel_classes")
    if not isinstance(rows, list) or len(rows) != class_count:
        raise ValueError("kernel class rows have the wrong count")
    if len(positions) != class_count or sorted(set(positions)) != positions:
        raise ValueError("kernel class positions are not strictly sorted")
    if 1 not in positions or central_class not in positions:
        raise ValueError("kernel carrier misses identity or central 3B")

    row_positions: list[int] = []
    size_sum = 0
    trace_sum = 0
    identity_count = 0
    central_count = 0
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("kernel class row must be an object")
        position = require_int(row, "position")
        size = require_int(row, "size")
        order = require_int(row, "order")
        class_trace = require_int(row, "trace")
        if position <= 0 or size <= 0 or order not in (1, 3):
            raise ValueError("invalid kernel class row")
        if order == 1:
            identity_count += 1
            if (position, size, class_trace) != (1, 1, degree):
                raise ValueError("invalid kernel identity row")
        if position == central_class:
            central_count += 1
            if (order, size, class_trace) != (3, 2, trace):
                raise ValueError("invalid kernel central row")
        row_positions.append(position)
        size_sum += size
        trace_sum += size * class_trace

    if row_positions != positions or identity_count != 1 or central_count != 1:
        raise ValueError("kernel class carrier reconstruction failed")
    if size_sum != kernel_order or trace_sum != invariant_numerator:
        raise ValueError("kernel rows fail size or trace reconstruction")

    return {
        "kernel_order": kernel_order,
        "kernel_class_count": class_count,
        "kernel_class_size_sum": class_size_sum,
        "kernel_position_checksum": sum(positions),
        "kernel_invariant_numerator": invariant_numerator,
        "kernel_invariant_dimension": invariant_dimension,
    }


def validate(payload: dict[str, Any]) -> dict[str, int]:
    require_true(payload, "classwise_reconstruction")
    degree = require_int(payload, "monster_character_degree")
    reconstructed = require_int(payload, "reconstructed_degree")
    trace = require_int(payload, "three_b_trace")
    invariant = require_int(payload, "invariant_multiplicity")
    zeta = require_int(payload, "zeta_multiplicity")
    zeta2 = require_int(payload, "zeta_squared_multiplicity")
    central_class = require_int(payload, "mn3b_central_3b_class_position")
    central_size = require_int(payload, "mn3b_central_3b_class_size")

    if (degree, reconstructed, trace, invariant, zeta, zeta2) != (
        EXPECTED_DEGREE,
        EXPECTED_DEGREE,
        EXPECTED_TRACE,
        EXPECTED_INVARIANT,
        EXPECTED_NONTRIVIAL,
        EXPECTED_NONTRIVIAL,
    ):
        raise ValueError("unexpected Monster restriction invariants")
    if invariant + zeta + zeta2 != degree or zeta + trace != invariant:
        raise ValueError("phase dimension or trace reconstruction failed")
    if central_size != 2:
        raise ValueError("central 3B class must have size two")

    phase = validate_phase_split(payload, central_class)
    kernel = validate_kernel(payload, degree, trace, central_class)
    return {
        "degree": degree,
        "trace": trace,
        "invariant": invariant,
        "zeta": zeta,
        "zeta2": zeta2,
        "central_class": central_class,
        "central_size": central_size,
        "source_class_count": require_int(payload, "source_class_count"),
        **phase,
        **kernel,
    }


def agda_module(values: dict[str, int], payload: dict[str, Any]) -> str:
    source = str(payload.get("source_table", "M")).replace('"', "")
    target = str(payload.get("target_table", "MN3B")).replace('"', "")
    return f'''module DASHI.Moonshine.Generated.Monster3BRestrictionCertificate where

-- GENERATED FILE. GAP + CTblLib checked classwise restriction, the actual
-- normal kernel class carrier, and the central-orbit Clifford degree split.
-- The paired normalizer constituents have degrees 1458*12 and 1458*78.
-- This does not compute the full 12- and 78-dimensional inertia characters.

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
contributionCertificate : constituentContributionSum ≡ monsterCharacterDegree
contributionCertificate = refl
centralClassSizeCertificate : centralThreeBClassSize ≡ 2
centralClassSizeCertificate = refl

extraspecialKernelOrder : Nat
extraspecialKernelOrder = {values['kernel_order']}
extraspecialKernelClassCount : Nat
extraspecialKernelClassCount = {values['kernel_class_count']}
extraspecialKernelClassSizeSum : Nat
extraspecialKernelClassSizeSum = {values['kernel_class_size_sum']}
extraspecialKernelClassPositionChecksum : Nat
extraspecialKernelClassPositionChecksum = {values['kernel_position_checksum']}
extraspecialKernelInvariantNumerator : Nat
extraspecialKernelInvariantNumerator = {values['kernel_invariant_numerator']}
extraspecialKernelInvariantDimension : Nat
extraspecialKernelInvariantDimension = {values['kernel_invariant_dimension']}
extraspecialKernelContainsCentralThreeB : Bool
extraspecialKernelContainsCentralThreeB = true
extraspecialKernelAllNonidentityOrdersThree : Bool
extraspecialKernelAllNonidentityOrdersThree = true

extraspecialKernelOrderCertificate : extraspecialKernelOrder ≡ 1594323
extraspecialKernelOrderCertificate = refl
extraspecialKernelClassSizeCertificate :
  extraspecialKernelClassSizeSum ≡ extraspecialKernelOrder
extraspecialKernelClassSizeCertificate = refl
extraspecialKernelAveragingCertificate :
  extraspecialKernelInvariantNumerator
  ≡ extraspecialKernelOrder * extraspecialKernelInvariantDimension
extraspecialKernelAveragingCertificate = refl

centreTrivialConstituentDegreeTotal : Nat
centreTrivialConstituentDegreeTotal = {values['centre_total']}
phasePairConstituentDegreeTotal : Nat
phasePairConstituentDegreeTotal = {values['pair_total']}
phasePairHeisenbergDegree : Nat
phasePairHeisenbergDegree = {values['pair_degree']}
firstMultiplicityDegree : Nat
firstMultiplicityDegree = {values['first_multiplicity_degree']}
secondMultiplicityDegree : Nat
secondMultiplicityDegree = {values['second_multiplicity_degree']}
firstPhasePairDegree : Nat
firstPhasePairDegree = {values['first_constituent_degree']}
secondPhasePairDegree : Nat
secondPhasePairDegree = {values['second_constituent_degree']}
phasePairConstituentCount : Nat
phasePairConstituentCount = {values['pair_constituent_count']}
phasePairDegreeChecksum : Nat
phasePairDegreeChecksum = {values['pair_checksum']}
twelvePlusSeventyEightDegreeSplitCertified : Bool
twelvePlusSeventyEightDegreeSplitCertified = true

cliffordDegreeReconstructionCertificate :
  centreTrivialConstituentDegreeTotal + phasePairConstituentDegreeTotal
  ≡ monsterCharacterDegree
cliffordDegreeReconstructionCertificate = refl
pairedSectorReconstructionCertificate :
  phasePairConstituentDegreeTotal ≡ 2 * zetaMultiplicity
pairedSectorReconstructionCertificate = refl
multiplicityDegreeSplitCertificate :
  firstMultiplicityDegree + secondMultiplicityDegree ≡ 90
multiplicityDegreeSplitCertificate = refl
firstPhasePairDegreeCertificate :
  phasePairHeisenbergDegree * firstMultiplicityDegree ≡ firstPhasePairDegree
firstPhasePairDegreeCertificate = refl
secondPhasePairDegreeCertificate :
  phasePairHeisenbergDegree * secondMultiplicityDegree ≡ secondPhasePairDegree
secondPhasePairDegreeCertificate = refl
phasePairBlockSumCertificate :
  firstPhasePairDegree + secondPhasePairDegree
  ≡ phasePairConstituentDegreeTotal
phasePairBlockSumCertificate = refl
phasePairTensorReconstructionCertificate :
  phasePairHeisenbergDegree *
    (firstMultiplicityDegree + secondMultiplicityDegree)
  ≡ phasePairConstituentDegreeTotal
phasePairTensorReconstructionCertificate = refl
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
