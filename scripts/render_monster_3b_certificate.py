#!/usr/bin/env python3
"""Render a fail-closed Agda certificate from the GAP/CTblLib MN3B result.

The GAP producer proves classwise reconstruction against the stored MN3B -> M
fusion, identifies the unique normal class union of order 3^13, computes the
full-character average over that actual extraspecial kernel, and classifies
every nonzero MN3B constituent by its trace on the size-two central 3B orbit.

The Clifford alternatives are checked independently here:

* centre-trivial: chi(z) = chi(1);
* paired nontrivial phases: 2 chi(z) = -chi(1).

For every paired-phase constituent, its degree must be divisible by 2*729.  The
expanded quotient multiset is required to be exactly [12, 78].  The renderer
then emits an Agda module whose dimension and branching arithmetic is kernel
checkable.  This certifies the actual normalizer-level paired multiplicity
split; it does not choose one of the conjugate zeta and zeta^2 sectors or build
a matrix intertwiner.
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
EXPECTED_KERNEL_ORDER = 3**13
EXPECTED_PHASE_PAIR_TOTAL = 2 * EXPECTED_NONTRIVIAL
EXPECTED_HEISENBERG_PAIR_DEGREE = 2 * 729
EXPECTED_MULTIPLICITY_DEGREES = [12, 78]
EXPECTED_PHASE_PAIR_DEGREES = [
    EXPECTED_HEISENBERG_PAIR_DEGREE * degree
    for degree in EXPECTED_MULTIPLICITY_DEGREES
]


def require_int(payload: dict[str, Any], key: str) -> int:
    value = payload.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be an integer")
    return value


def require_true(payload: dict[str, Any], key: str) -> None:
    if payload.get(key) is not True:
        raise ValueError(f"{key} must be true")


def require_int_list(payload: dict[str, Any], key: str) -> list[int]:
    values = payload.get(key)
    if not isinstance(values, list):
        raise ValueError(f"{key} must be a list")
    if any(not isinstance(value, int) or isinstance(value, bool) for value in values):
        raise ValueError(f"{key} must contain only integers")
    return values


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

    centre_trivial_total = require_int(
        payload, "centre_trivial_constituent_degree_total"
    )
    phase_pair_total = require_int(payload, "phase_pair_constituent_degree_total")
    heisenberg_pair_degree = require_int(payload, "phase_pair_heisenberg_degree")
    multiplicity_degrees = require_int_list(
        payload, "phase_pair_multiplicity_degrees"
    )
    require_true(payload, "twelve_plus_seventy_eight_certified")

    if centre_trivial_total != EXPECTED_INVARIANT:
        raise ValueError("centre-trivial constituents do not have degree 65663")
    if phase_pair_total != EXPECTED_PHASE_PAIR_TOTAL:
        raise ValueError("paired-phase constituents do not have degree 131220")
    if centre_trivial_total + phase_pair_total != degree:
        raise ValueError("Clifford constituent totals do not reconstruct degree")
    if heisenberg_pair_degree != EXPECTED_HEISENBERG_PAIR_DEGREE:
        raise ValueError("paired Heisenberg degree is not 2*729")
    if multiplicity_degrees != EXPECTED_MULTIPLICITY_DEGREES:
        raise ValueError("actual multiplicity degrees are not exactly [12, 78]")
    if sum(multiplicity_degrees) != 90:
        raise ValueError("actual multiplicity degrees do not sum to 90")
    if heisenberg_pair_degree * sum(multiplicity_degrees) != phase_pair_total:
        raise ValueError("paired Heisenberg reconstruction failed")

    constituents = payload.get("constituents")
    if not isinstance(constituents, list) or not constituents:
        raise ValueError("constituents must be a nonempty list")

    contribution_sum = 0
    weighted_checksum = 0
    centre_trivial_row_total = 0
    phase_pair_row_total = 0
    constituent_positions: list[int] = []
    paired_positions_from_all_rows: list[int] = []

    for row in constituents:
        if not isinstance(row, dict):
            raise ValueError("constituent row must be an object")
        position = require_int(row, "position")
        multiplicity = require_int(row, "multiplicity")
        constituent_degree = require_int(row, "degree")
        central_trace = require_int(row, "central_trace")
        contribution = require_int(row, "contribution")
        clifford_type = row.get("clifford_type")

        if position <= 0 or multiplicity <= 0 or constituent_degree <= 0:
            raise ValueError("constituent data must be positive")
        if multiplicity * constituent_degree != contribution:
            raise ValueError("constituent contribution mismatch")
        if clifford_type == "centre-trivial":
            if central_trace != constituent_degree:
                raise ValueError("centre-trivial constituent has wrong central trace")
            centre_trivial_row_total += contribution
        elif clifford_type == "paired-phase":
            if 2 * central_trace != -constituent_degree:
                raise ValueError("paired-phase constituent has wrong central trace")
            if constituent_degree % heisenberg_pair_degree != 0:
                raise ValueError("paired-phase degree is not divisible by 2*729")
            phase_pair_row_total += contribution
            paired_positions_from_all_rows.append(position)
        else:
            raise ValueError("unknown Clifford constituent type")

        contribution_sum += contribution
        weighted_checksum += position * contribution
        constituent_positions.append(position)

    if len(set(constituent_positions)) != len(constituent_positions):
        raise ValueError("constituent positions must be unique")
    if contribution_sum != degree:
        raise ValueError("constituent contributions do not reconstruct degree")
    if centre_trivial_row_total != centre_trivial_total:
        raise ValueError("centre-trivial rows do not reconstruct their total")
    if phase_pair_row_total != phase_pair_total:
        raise ValueError("paired-phase rows do not reconstruct their total")

    phase_pair_rows = payload.get("phase_pair_constituents")
    if not isinstance(phase_pair_rows, list) or not phase_pair_rows:
        raise ValueError("phase_pair_constituents must be a nonempty list")

    phase_pair_positions: list[int] = []
    expanded_multiplicity_degrees: list[int] = []
    phase_pair_contribution_sum = 0
    phase_pair_degree_checksum = 0

    for row in phase_pair_rows:
        if not isinstance(row, dict):
            raise ValueError("phase-pair row must be an object")
        position = require_int(row, "position")
        multiplicity = require_int(row, "multiplicity")
        constituent_degree = require_int(row, "degree")
        central_trace = require_int(row, "central_trace")
        multiplicity_degree = require_int(row, "multiplicity_degree")
        contribution = require_int(row, "contribution")

        if position <= 0 or multiplicity <= 0 or multiplicity_degree <= 0:
            raise ValueError("phase-pair row data must be positive")
        if 2 * central_trace != -constituent_degree:
            raise ValueError("phase-pair central trace ratio failed")
        if constituent_degree != heisenberg_pair_degree * multiplicity_degree:
            raise ValueError("phase-pair degree does not equal 2*729*m")
        if contribution != multiplicity * constituent_degree:
            raise ValueError("phase-pair contribution mismatch")

        phase_pair_positions.append(position)
        phase_pair_contribution_sum += contribution
        phase_pair_degree_checksum += position * contribution
        expanded_multiplicity_degrees.extend([multiplicity_degree] * multiplicity)

    if len(set(phase_pair_positions)) != len(phase_pair_positions):
        raise ValueError("phase-pair positions must be unique")
    if phase_pair_positions != paired_positions_from_all_rows:
        raise ValueError("phase-pair rows disagree with the full constituent rows")
    if phase_pair_contribution_sum != phase_pair_total:
        raise ValueError("phase-pair rows do not reconstruct degree 131220")
    if sorted(expanded_multiplicity_degrees) != EXPECTED_MULTIPLICITY_DEGREES:
        raise ValueError("expanded actual multiplicity degrees are not [12, 78]")

    actual_phase_pair_degrees = sorted(
        heisenberg_pair_degree * value for value in expanded_multiplicity_degrees
    )
    if actual_phase_pair_degrees != EXPECTED_PHASE_PAIR_DEGREES:
        raise ValueError("actual paired constituent degrees are not 17496 and 113724")

    kernel_order = require_int(payload, "extraspecial_kernel_order")
    kernel_class_count = require_int(payload, "extraspecial_kernel_class_count")
    kernel_class_size_sum = require_int(
        payload, "extraspecial_kernel_class_size_sum"
    )
    kernel_invariant_numerator = require_int(
        payload, "extraspecial_kernel_invariant_numerator"
    )
    kernel_invariant_dimension = require_int(
        payload, "extraspecial_kernel_invariant_dimension"
    )
    require_true(payload, "extraspecial_kernel_contains_central_3b")
    require_true(payload, "extraspecial_kernel_all_nonidentity_orders_three")

    if kernel_order != EXPECTED_KERNEL_ORDER:
        raise ValueError("extraspecial kernel order is not 3^13")
    if kernel_class_size_sum != kernel_order:
        raise ValueError("extraspecial kernel class sizes do not sum to its order")
    if kernel_invariant_dimension < 0:
        raise ValueError("extraspecial kernel invariant dimension is negative")
    if kernel_invariant_numerator != kernel_order * kernel_invariant_dimension:
        raise ValueError("extraspecial kernel averaging identity failed")

    kernel_positions = require_int_list(payload, "extraspecial_kernel_class_positions")
    if len(kernel_positions) != kernel_class_count:
        raise ValueError("kernel class-position count mismatch")
    if sorted(set(kernel_positions)) != kernel_positions:
        raise ValueError("kernel class positions must be strictly sorted")
    if 1 not in kernel_positions or central_class not in kernel_positions:
        raise ValueError("kernel class carrier misses identity or central 3B")

    kernel_rows = payload.get("extraspecial_kernel_classes")
    if not isinstance(kernel_rows, list):
        raise ValueError("extraspecial_kernel_classes must be a list")
    if len(kernel_rows) != kernel_class_count:
        raise ValueError("kernel class-row count mismatch")

    row_positions: list[int] = []
    row_size_sum = 0
    row_trace_numerator = 0
    identity_rows = 0
    central_rows = 0
    for row in kernel_rows:
        if not isinstance(row, dict):
            raise ValueError("kernel class row must be an object")
        position = require_int(row, "position")
        size = require_int(row, "size")
        order = require_int(row, "order")
        class_trace = require_int(row, "trace")
        if position <= 0 or size <= 0:
            raise ValueError("kernel class position and size must be positive")
        if order not in (1, 3):
            raise ValueError("kernel class order must be one or three")
        if order == 1:
            identity_rows += 1
            if position != 1 or size != 1 or class_trace != degree:
                raise ValueError("invalid identity row in kernel class data")
        if position == central_class:
            central_rows += 1
            if order != 3 or size != 2 or class_trace != trace:
                raise ValueError("invalid central 3B row in kernel class data")
        row_positions.append(position)
        row_size_sum += size
        row_trace_numerator += size * class_trace

    if row_positions != kernel_positions:
        raise ValueError("kernel rows and class-position list disagree")
    if identity_rows != 1 or central_rows != 1:
        raise ValueError("kernel rows must contain one identity and one central row")
    if row_size_sum != kernel_order:
        raise ValueError("kernel row sizes do not reconstruct kernel order")
    if row_trace_numerator != kernel_invariant_numerator:
        raise ValueError("kernel row traces do not reconstruct averaging numerator")

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
        "kernel_order": kernel_order,
        "kernel_class_count": kernel_class_count,
        "kernel_class_size_sum": kernel_class_size_sum,
        "kernel_position_checksum": sum(kernel_positions),
        "kernel_invariant_numerator": kernel_invariant_numerator,
        "kernel_invariant_dimension": kernel_invariant_dimension,
        "centre_trivial_total": centre_trivial_total,
        "phase_pair_total": phase_pair_total,
        "heisenberg_pair_degree": heisenberg_pair_degree,
        "first_multiplicity_degree": multiplicity_degrees[0],
        "second_multiplicity_degree": multiplicity_degrees[1],
        "first_phase_pair_degree": actual_phase_pair_degrees[0],
        "second_phase_pair_degree": actual_phase_pair_degrees[1],
        "phase_pair_constituent_count": len(phase_pair_rows),
        "phase_pair_degree_checksum": phase_pair_degree_checksum,
    }


def agda_module(values: dict[str, int], payload: dict[str, Any]) -> str:
    source = str(payload.get("source_table", "M")).replace('"', "")
    target = str(payload.get("target_table", "MN3B")).replace('"', "")
    return f'''module DASHI.Moonshine.Generated.Monster3BRestrictionCertificate where

-- GENERATED FILE. Source: GAP + CTblLib stored class fusion, ordinary
-- character-table normal-subgroup data, and central-orbit Clifford
-- classification of every nonzero constituent.
--
-- The producer checked nonnegative integral multiplicities, equality on every
-- MN3B conjugacy-class value, the unique normal class union of order 3^13, and
-- the two possible central trace ratios. The paired-phase irreducible degrees
-- are exactly 2*729*12 and 2*729*78. This is an actual normalizer-character
-- statement; it does not choose a zeta-sector basis or construct matrices.

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
centreTrivialConstituentDegreeTotal = {values['centre_trivial_total']}

phasePairConstituentDegreeTotal : Nat
phasePairConstituentDegreeTotal = {values['phase_pair_total']}

phasePairHeisenbergDegree : Nat
phasePairHeisenbergDegree = {values['heisenberg_pair_degree']}

firstMultiplicityDegree : Nat
firstMultiplicityDegree = {values['first_multiplicity_degree']}

secondMultiplicityDegree : Nat
secondMultiplicityDegree = {values['second_multiplicity_degree']}

firstPhasePairDegree : Nat
firstPhasePairDegree = {values['first_phase_pair_degree']}

secondPhasePairDegree : Nat
secondPhasePairDegree = {values['second_phase_pair_degree']}

phasePairConstituentCount : Nat
phasePairConstituentCount = {values['phase_pair_constituent_count']}

phasePairDegreeChecksum : Nat
phasePairDegreeChecksum = {values['phase_pair_degree_checksum']}

twelvePlusSeventyEightCertified : Bool
twelvePlusSeventyEightCertified = true

cliffordDegreeReconstructionCertificate :
  centreTrivialConstituentDegreeTotal + phasePairConstituentDegreeTotal
  ≡ monsterCharacterDegree
cliffordDegreeReconstructionCertificate = refl

pairedSectorReconstructionCertificate :
  phasePairConstituentDegreeTotal ≡ 2 * zetaMultiplicity
pairedSectorReconstructionCertificate = refl

multiplicitySplitCertificate :
  firstMultiplicityDegree + secondMultiplicityDegree ≡ 90
multiplicitySplitCertificate = refl

firstPhasePairDegreeCertificate :
  phasePairHeisenbergDegree * firstMultiplicityDegree
  ≡ firstPhasePairDegree
firstPhasePairDegreeCertificate = refl

secondPhasePairDegreeCertificate :
  phasePairHeisenbergDegree * secondMultiplicityDegree
  ≡ secondPhasePairDegree
secondPhasePairDegreeCertificate = refl

phasePairBlockSumCertificate :
  firstPhasePairDegree + secondPhasePairDegree
  ≡ phasePairConstituentDegreeTotal
phasePairBlockSumCertificate = refl

phasePairTensorReconstructionCertificate :
  phasePairHeisenbergDegree
  * (firstMultiplicityDegree + secondMultiplicityDegree)
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
