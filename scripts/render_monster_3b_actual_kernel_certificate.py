#!/usr/bin/env python3
"""Combine actual MN3B group structure with the validated CTblLib restriction.

The restriction side is validated by the single authority in
``render_monster_3b_certificate``.  This script adds the independently
constructed group and verifies that its extraspecial centre is the same MN3B
class used by the Monster restriction and the same class fused to Monster 3B.

The combined artifact certifies the actual paired multiplicity-degree split
12+78.  It deliberately leaves the full inertia-character equality and module
intertwiner false until those class values and maps are constructed.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from render_monster_3b_certificate import validate as validate_restriction

EXPECTED_GROUP_ORDER = 2_859_230_155_080_499_200
EXPECTED_KERNEL_ORDER = 1_594_323
EXPECTED_QUOTIENT_ORDER = 531_441
EXPECTED_HEISENBERG_DEGREE = 729
EXPECTED_PHASE_PAIR_DEGREE = 2 * EXPECTED_HEISENBERG_DEGREE


def integer(payload: dict[str, Any], key: str) -> int:
    value = payload.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be an integer")
    return value


def truth(payload: dict[str, Any], key: str) -> None:
    if payload.get(key) is not True:
        raise ValueError(f"{key} must be true")


def text(payload: dict[str, Any], key: str) -> str:
    value = payload.get(key)
    if not isinstance(value, str) or not value:
        raise ValueError(f"{key} must be a nonempty string")
    return value


def validate_kernel(payload: dict[str, Any]) -> dict[str, Any]:
    for key in (
        "actual_kernel_normal",
        "derived_equals_centre",
        "quotient_elementary_abelian",
        "centre_orbit_is_all_nonidentity_centre",
        "centre_class_fuses_to_monster_3b",
    ):
        truth(payload, key)

    values: dict[str, Any] = {
        "construction_source": text(payload, "construction_source"),
        "group_name": text(payload, "atlas_group_name"),
        "representation_name": text(payload, "atlas_representation_name"),
        "group_order": integer(payload, "actual_group_order"),
        "kernel_order": integer(payload, "actual_kernel_order"),
        "kernel_exponent": integer(payload, "actual_kernel_exponent"),
        "centre_order": integer(payload, "actual_kernel_centre_order"),
        "derived_order": integer(payload, "actual_kernel_derived_order"),
        "quotient_order": integer(payload, "actual_kernel_quotient_order"),
        "centre_orbit_size": integer(payload, "nonidentity_centre_orbit_size"),
        "central_class": integer(payload, "mn3b_central_class_position"),
        "central_class_order": integer(payload, "mn3b_central_class_order"),
        "central_class_size": integer(payload, "mn3b_central_class_size"),
        "monster_3b_class": integer(payload, "monster_3b_class_position"),
        "linear_count": integer(payload, "linear_character_count"),
        "nonlinear_count": integer(payload, "nonlinear_character_count"),
        "nonlinear_degree": integer(payload, "nonlinear_character_degree"),
        "square_sum": integer(payload, "character_degree_square_sum"),
    }

    expected = {
        "group_order": EXPECTED_GROUP_ORDER,
        "kernel_order": EXPECTED_KERNEL_ORDER,
        "kernel_exponent": 3,
        "centre_order": 3,
        "derived_order": 3,
        "quotient_order": EXPECTED_QUOTIENT_ORDER,
        "centre_orbit_size": 2,
        "central_class_order": 3,
        "central_class_size": 2,
        "linear_count": EXPECTED_QUOTIENT_ORDER,
        "nonlinear_count": 2,
        "nonlinear_degree": EXPECTED_HEISENBERG_DEGREE,
        "square_sum": EXPECTED_KERNEL_ORDER,
    }
    for key, expected_value in expected.items():
        if values[key] != expected_value:
            raise ValueError(f"unexpected {key}: {values[key]}")
    return values


def combine(kernel_payload: dict[str, Any], restriction_payload: dict[str, Any]) -> dict[str, Any]:
    kernel = validate_kernel(kernel_payload)
    restriction = validate_restriction(restriction_payload)

    if kernel["central_class"] != restriction["central_class"]:
        raise ValueError("group centre and restriction use different MN3B classes")
    restriction_monster_class = integer(
        restriction_payload, "monster_3b_class_position"
    )
    if kernel["monster_3b_class"] != restriction_monster_class:
        raise ValueError("group and restriction disagree on the Monster 3B image")
    if kernel["kernel_order"] != restriction["kernel_order"]:
        raise ValueError("group and table certificates disagree on kernel order")
    if restriction["pair_degree"] != EXPECTED_PHASE_PAIR_DEGREE:
        raise ValueError("restriction paired degree is not 2*729")

    return {
        **kernel,
        "monster_degree": restriction["degree"],
        "trace": restriction["trace"],
        "invariant": restriction["invariant"],
        "zeta": restriction["zeta"],
        "zeta2": restriction["zeta2"],
        "heisenberg_degree": EXPECTED_HEISENBERG_DEGREE,
        "heisenberg_multiplicity": 90,
        "zeta_degree_reconstruction": 90 * EXPECTED_HEISENBERG_DEGREE,
        "centre_trivial_total": restriction["centre_total"],
        "phase_pair_total": restriction["pair_total"],
        "phase_pair_heisenberg_degree": restriction["pair_degree"],
        "first_multiplicity_degree": restriction["first_multiplicity_degree"],
        "second_multiplicity_degree": restriction["second_multiplicity_degree"],
        "first_phase_pair_degree": restriction["first_constituent_degree"],
        "second_phase_pair_degree": restriction["second_constituent_degree"],
        "actual_kernel_and_restriction_class_aligned": True,
        "extraspecial_structure_certified": True,
        "actual_multiplicity_degree_split_certified": True,
        "actual_multiplicity_character_computed": False,
        "twelve_plus_seventy_eight_character_equality_proved": False,
    }


def agda_module(values: dict[str, Any]) -> str:
    construction = values["construction_source"].replace('"', "")
    group_name = values["group_name"].replace('"', "")
    representation = values["representation_name"].replace('"', "")
    return f'''module DASHI.Moonshine.Generated.Monster3BActualKernelCertificate where

-- GENERATED FILE.  A constructible MN3B group and the CTblLib restriction
-- independently selected the same size-two centre class and Monster 3B image.
-- The actual paired normalizer constituents have multiplicity degrees 12 and
-- 78.  Their complete inertia characters and an explicit intertwiner remain
-- separate obligations.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

constructionSource : String
constructionSource = "{construction}"
constructedGroupName : String
constructedGroupName = "{group_name}"
constructedRepresentationName : String
constructedRepresentationName = "{representation}"

actualNormalizerOrder : Nat
actualNormalizerOrder = {values['group_order']}
actualKernelOrder : Nat
actualKernelOrder = {values['kernel_order']}
actualKernelExponent : Nat
actualKernelExponent = {values['kernel_exponent']}
actualKernelCentreOrder : Nat
actualKernelCentreOrder = {values['centre_order']}
actualKernelDerivedOrder : Nat
actualKernelDerivedOrder = {values['derived_order']}
actualKernelQuotientOrder : Nat
actualKernelQuotientOrder = {values['quotient_order']}
centralOrbitSize : Nat
centralOrbitSize = {values['centre_orbit_size']}
mn3bCentralClassPosition : Nat
mn3bCentralClassPosition = {values['central_class']}
monsterThreeBClassPosition : Nat
monsterThreeBClassPosition = {values['monster_3b_class']}

monsterCharacterDegree : Nat
monsterCharacterDegree = {values['monster_degree']}
threeBTrace : Nat
threeBTrace = {values['trace']}
zetaSectorDegree : Nat
zetaSectorDegree = {values['zeta']}
zetaSquaredSectorDegree : Nat
zetaSquaredSectorDegree = {values['zeta2']}
heisenbergDegree : Nat
heisenbergDegree = {values['heisenberg_degree']}
heisenbergMultiplicity : Nat
heisenbergMultiplicity = {values['heisenberg_multiplicity']}
linearCharacterCount : Nat
linearCharacterCount = {values['linear_count']}
nonlinearCharacterCount : Nat
nonlinearCharacterCount = {values['nonlinear_count']}

centreTrivialConstituentDegreeTotal : Nat
centreTrivialConstituentDegreeTotal = {values['centre_trivial_total']}
phasePairConstituentDegreeTotal : Nat
phasePairConstituentDegreeTotal = {values['phase_pair_total']}
phasePairHeisenbergDegree : Nat
phasePairHeisenbergDegree = {values['phase_pair_heisenberg_degree']}
firstMultiplicityDegree : Nat
firstMultiplicityDegree = {values['first_multiplicity_degree']}
secondMultiplicityDegree : Nat
secondMultiplicityDegree = {values['second_multiplicity_degree']}
firstPhasePairDegree : Nat
firstPhasePairDegree = {values['first_phase_pair_degree']}
secondPhasePairDegree : Nat
secondPhasePairDegree = {values['second_phase_pair_degree']}

extraspecialStructureCertified : Bool
extraspecialStructureCertified = true
actualKernelAndRestrictionClassAligned : Bool
actualKernelAndRestrictionClassAligned = true
actualMultiplicityDegreeSplitCertified : Bool
actualMultiplicityDegreeSplitCertified = true
actualMultiplicityCharacterComputed : Bool
actualMultiplicityCharacterComputed = false
twelvePlusSeventyEightCharacterEqualityProved : Bool
twelvePlusSeventyEightCharacterEqualityProved = false

kernelOrderCertificate : actualKernelOrder ≡ 1594323
kernelOrderCertificate = refl
quotientOrderCertificate : actualKernelQuotientOrder ≡ 531441
quotientOrderCertificate = refl
centreDerivedCertificate :
  actualKernelCentreOrder + actualKernelDerivedOrder ≡ 6
centreDerivedCertificate = refl
extraspecialDegreeSquareCertificate :
  linearCharacterCount
  + nonlinearCharacterCount * heisenbergDegree * heisenbergDegree
  ≡ actualKernelOrder
extraspecialDegreeSquareCertificate = refl
zetaSectorRecognitionArithmetic :
  heisenbergMultiplicity * heisenbergDegree ≡ zetaSectorDegree
zetaSectorRecognitionArithmetic = refl
monsterPhaseDimensionCertificate :
  65663 + zetaSectorDegree + zetaSquaredSectorDegree
  ≡ monsterCharacterDegree
monsterPhaseDimensionCertificate = refl
threeBTraceCertificate : zetaSectorDegree + threeBTrace ≡ 65663
threeBTraceCertificate = refl
centralOrbitCertificate : centralOrbitSize ≡ 2
centralOrbitCertificate = refl

cliffordDegreeCertificate :
  centreTrivialConstituentDegreeTotal + phasePairConstituentDegreeTotal
  ≡ monsterCharacterDegree
cliffordDegreeCertificate = refl
pairedSectorCertificate :
  phasePairConstituentDegreeTotal ≡ 2 * zetaSectorDegree
pairedSectorCertificate = refl
phasePairHeisenbergCertificate :
  phasePairHeisenbergDegree ≡ 2 * heisenbergDegree
phasePairHeisenbergCertificate = refl
multiplicityDegreeSplitCertificate :
  firstMultiplicityDegree + secondMultiplicityDegree ≡ heisenbergMultiplicity
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
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("kernel_json", type=Path)
    parser.add_argument("restriction_json", type=Path)
    parser.add_argument("combined_json", type=Path)
    parser.add_argument("agda_output", type=Path)
    args = parser.parse_args()

    kernel = json.loads(args.kernel_json.read_text())
    restriction = json.loads(args.restriction_json.read_text())
    values = combine(kernel, restriction)

    args.combined_json.parent.mkdir(parents=True, exist_ok=True)
    args.combined_json.write_text(json.dumps(values, indent=2, sort_keys=True) + "\n")
    args.agda_output.parent.mkdir(parents=True, exist_ok=True)
    args.agda_output.write_text(agda_module(values))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
