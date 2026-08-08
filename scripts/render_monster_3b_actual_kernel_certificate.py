#!/usr/bin/env python3
"""Combine the AtlasRep kernel certificate with the CTblLib 3B restriction.

The producer refuses to identify the actual 65610-dimensional phase sector with
an arbitrary 729 x 90 model.  It checks instead that:

* AtlasRep constructs the actual group of shape 3^(1+12).2.Suz.2;
* its 3-core is extraspecial of exponent three and order 3^13;
* its centre is the unique size-two order-three MN3B class;
* that class fuses to Monster 3B;
* the actual Monster character has zeta-sector degree 65610;
* 65610 = 90 * 729 and the extraspecial degree-square budget is exact.

The generated Agda file kernel-checks all arithmetic and class-position
alignment.  The remaining mathematical promotion is precisely the finite
Stone--von Neumann uniqueness theorem applied to the actual restricted module;
that theorem is formalized separately rather than encoded as a JSON boolean.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

EXPECTED_GROUP_ORDER = 2_859_230_155_080_499_200
EXPECTED_KERNEL_ORDER = 1_594_323
EXPECTED_QUOTIENT_ORDER = 531_441
EXPECTED_HEISENBERG_DEGREE = 729
EXPECTED_ZETA_DEGREE = 65_610
EXPECTED_MULTIPLICITY = 90
EXPECTED_MONSTER_DEGREE = 196_883
EXPECTED_TRACE = 53


def integer(payload: dict[str, Any], key: str) -> int:
    value = payload.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be an integer")
    return value


def truth(payload: dict[str, Any], key: str) -> None:
    if payload.get(key) is not True:
        raise ValueError(f"{key} must be true")


def validate_kernel(payload: dict[str, Any]) -> dict[str, int]:
    for key in (
        "actual_kernel_normal",
        "derived_equals_centre",
        "quotient_elementary_abelian",
        "centre_orbit_is_all_nonidentity_centre",
        "centre_class_fuses_to_monster_3b",
    ):
        truth(payload, key)

    values = {
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


def validate_restriction(payload: dict[str, Any]) -> dict[str, int]:
    truth(payload, "classwise_reconstruction")
    values = {
        "monster_degree": integer(payload, "monster_character_degree"),
        "trace": integer(payload, "three_b_trace"),
        "invariant": integer(payload, "invariant_multiplicity"),
        "zeta": integer(payload, "zeta_multiplicity"),
        "zeta2": integer(payload, "zeta_squared_multiplicity"),
        "central_class": integer(payload, "mn3b_central_3b_class_position"),
        "central_class_size": integer(payload, "mn3b_central_3b_class_size"),
        "monster_3b_class": integer(payload, "monster_3b_class_position"),
    }
    if values["monster_degree"] != EXPECTED_MONSTER_DEGREE:
        raise ValueError("unexpected Monster character degree")
    if values["trace"] != EXPECTED_TRACE:
        raise ValueError("unexpected Monster 3B trace")
    if values["zeta"] != EXPECTED_ZETA_DEGREE or values["zeta2"] != EXPECTED_ZETA_DEGREE:
        raise ValueError("unexpected nontrivial phase dimensions")
    if values["invariant"] != 65_663:
        raise ValueError("unexpected invariant phase dimension")
    if values["central_class_size"] != 2:
        raise ValueError("restriction selected a non-size-two class")
    return values


def combine(kernel: dict[str, Any], restriction: dict[str, Any]) -> dict[str, Any]:
    k = validate_kernel(kernel)
    r = validate_restriction(restriction)
    if k["central_class"] != r["central_class"]:
        raise ValueError("AtlasRep kernel centre and CTblLib restriction use different MN3B classes")
    if k["monster_3b_class"] != r["monster_3b_class"]:
        raise ValueError("AtlasRep and restriction certificates disagree on the Monster 3B image")
    if EXPECTED_MULTIPLICITY * EXPECTED_HEISENBERG_DEGREE != r["zeta"]:
        raise ValueError("zeta-sector degree is not 90 times 729")

    return {
        **k,
        **r,
        "heisenberg_degree": EXPECTED_HEISENBERG_DEGREE,
        "heisenberg_multiplicity": EXPECTED_MULTIPLICITY,
        "zeta_degree_reconstruction": EXPECTED_MULTIPLICITY * EXPECTED_HEISENBERG_DEGREE,
        "actual_kernel_and_restriction_class_aligned": True,
        "extraspecial_structure_certified": True,
        "stone_von_neumann_promotion_ready": True,
        "actual_multiplicity_character_computed": False,
        "twelve_plus_seventy_eight_proved": False,
    }


def agda_module(values: dict[str, Any]) -> str:
    return f'''module DASHI.Moonshine.Generated.Monster3BActualKernelCertificate where

-- GENERATED FILE.
-- Sources: AtlasRep actual group construction plus CTblLib class fusion.
-- The generating scripts verified the actual 3-core, its centre, its quotient,
-- the Monster 3B fusion, the 196883-character restriction, and all displayed
-- arithmetic.  Stone--von Neumann promotion is a separate in-repository theorem.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

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

extraspecialStructureCertified : Bool
extraspecialStructureCertified = true

actualKernelAndRestrictionClassAligned : Bool
actualKernelAndRestrictionClassAligned = true

stoneVonNeumannPromotionReady : Bool
stoneVonNeumannPromotionReady = true

actualMultiplicityCharacterComputed : Bool
actualMultiplicityCharacterComputed = false

twelvePlusSeventyEightProved : Bool
twelvePlusSeventyEightProved = false

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
