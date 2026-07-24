#!/usr/bin/env python3
"""Emit an Agda bridge from a generated path LDL certificate to a literal fibre."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


def right_sum(terms: list[str], zero_tail: bool = False) -> str:
    if not terms:
        return "0ℚ"
    result = "0ℚ" if zero_tail else terms[-1]
    source = reversed(terms) if zero_tail else reversed(terms[:-1])
    for term in source:
        result = f"({term} + {result})"
    return result


def cyclic_index(index: int) -> str:
    result = "zeroᵢ"
    for _ in range(index):
        result = f"sucᵢ ({result})"
    return result


def validate_module_name(module_name: str) -> None:
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_.]*", module_name):
        raise ValueError(f"invalid Agda module name: {module_name!r}")


def generate_bridge(
    length: int,
    certificate_module: str,
    bridge_module: str,
) -> str:
    if length < 2:
        raise ValueError("path length must be at least two")
    validate_module_name(certificate_module)
    validate_module_name(bridge_module)

    indices = [f"index{index}" for index in range(length)]
    physical = [
        f"physicalCoordinate field axis transverse {index_name}"
        for index_name in indices
    ]
    independent = physical[:-1]
    final = physical[-1]
    prefix = right_sum(independent)
    generated_final = f"(- {prefix})"
    total_with_zero = right_sum(physical, zero_tail=True)

    coordinate_arguments = "\n    ".join(independent)
    isolate_arguments = " ".join(f"c{index}" for index in range(length))
    isolate_physical_arguments = "\n    ".join(physical)
    total_variables = [f"c{index}" for index in range(length)]
    total_variable_expression = right_sum(total_variables, zero_tail=True)
    prefix_variable_expression = right_sum(total_variables[:-1])

    norm_physical = right_sum([f"sq ({value})" for value in physical], zero_tail=True)
    norm_substituted = right_sum(
        [f"sq ({value})" for value in independent] + [f"sq ({generated_final})"],
        zero_tail=True,
    )
    energy_terms = [
        f"sq ({physical[index + 1]} - {physical[index]})"
        for index in range(length - 1)
    ]
    energy_physical = right_sum(energy_terms, zero_tail=True)
    energy_substituted_terms = [
        f"sq ({independent[index + 1]} - {independent[index]})"
        for index in range(length - 2)
    ] + [f"sq ({generated_final} - {independent[-1]})"]
    energy_substituted = right_sum(energy_substituted_terms, zero_tail=True)

    ring_arguments = "\n        ".join(independent + [generated_final])
    index_declarations = "\n".join(
        f"{name} : CyclicIndex sideLength\n{name} = {cyclic_index(index)}"
        for index, name in enumerate(indices)
    )

    return f'''module {bridge_module} where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import {certificate_module}

sideLength : Nat
sideLength = {length}

{index_declarations}

physicalCoordinate :
  SiteField sideLength → Axis4 → Triple (CyclicIndex sideLength) →
  CyclicIndex sideLength → ℚ
physicalCoordinate field axis transverse =
  scaledCenteredFibreValue field axis transverse

coordinatesFromPhysicalFibre :
  SiteField sideLength → Axis4 → Triple (CyclicIndex sideLength) →
  PathCoordinates
coordinatesFromPhysicalFibre field axis transverse =
  pathCoordinates
    {coordinate_arguments}

generatedFinalCoordinate :
  SiteField sideLength → Axis4 → Triple (CyclicIndex sideLength) → ℚ
generatedFinalCoordinate field axis transverse = {generated_final}

isolateFinalFromZero : ∀ {isolate_arguments} →
  {total_variable_expression} ≡ 0ℚ →
  c{length - 1} ≡ - ({prefix_variable_expression})
isolateFinalFromZero {isolate_arguments} total =
  let
    isolate :
      c{length - 1}
      ≡ {total_variable_expression} - ({prefix_variable_expression})
    isolate = ℚRing.solve-∀ {isolate_arguments}

    zeroReduction :
      0ℚ - ({prefix_variable_expression})
      ≡ - ({prefix_variable_expression})
    zeroReduction = ℚRing.solve-∀ {' '.join(total_variables[:-1])}
  in
  trans isolate
    (trans
      (cong (λ value → value - ({prefix_variable_expression})) total)
      zeroReduction)

physicalFinalCoordinateIsGenerated :
  ∀ field axis transverse →
  {final}
  ≡ generatedFinalCoordinate field axis transverse
physicalFinalCoordinateIsGenerated field axis transverse =
  isolateFinalFromZero
    {isolate_physical_arguments}
    (scaledCenteredFibreSumZero field axis transverse)

physicalNormExpansion :
  ∀ field axis transverse →
  scaledCenteredFibreNormSq field axis transverse
  ≡ {norm_physical}
physicalNormExpansion field axis transverse = refl

physicalEnergyExpansion :
  ∀ field axis transverse →
  scaledCenteredFibreEdgeEnergy field axis transverse
  ≡ {energy_physical}
physicalEnergyExpansion field axis transverse = refl

physicalNormMatchesGenerated :
  ∀ field axis transverse →
  scaledCenteredFibreNormSq field axis transverse
  ≡ pathNormSq (coordinatesFromPhysicalFibre field axis transverse)
physicalNormMatchesGenerated field axis transverse =
  trans
    (physicalNormExpansion field axis transverse)
    (subst
      (λ finalValue →
        {norm_physical.replace(final, 'finalValue')}
        ≡ pathNormSq (coordinatesFromPhysicalFibre field axis transverse))
      (physicalFinalCoordinateIsGenerated field axis transverse)
      (ℚRing.solve-∀
        {ring_arguments}))

physicalEnergyMatchesGenerated :
  ∀ field axis transverse →
  scaledCenteredFibreEdgeEnergy field axis transverse
  ≡ pathEnergy (coordinatesFromPhysicalFibre field axis transverse)
physicalEnergyMatchesGenerated field axis transverse =
  trans
    (physicalEnergyExpansion field axis transverse)
    (subst
      (λ finalValue →
        {energy_physical.replace(final, 'finalValue')}
        ≡ pathEnergy (coordinatesFromPhysicalFibre field axis transverse))
      (physicalFinalCoordinateIsGenerated field axis transverse)
      (ℚRing.solve-∀
        {ring_arguments}))

physicalFibrePoincare :
  ∀ field axis transverse →
  coercivityConstant * scaledCenteredFibreNormSq field axis transverse
  ≤ scaledCenteredFibreEdgeEnergy field axis transverse
physicalFibrePoincare field axis transverse =
  subst
    (λ energyValue →
      coercivityConstant * scaledCenteredFibreNormSq field axis transverse
      ≤ energyValue)
    (sym (physicalEnergyMatchesGenerated field axis transverse))
    (subst
      (λ normValue →
        coercivityConstant * normValue
        ≤ pathEnergy (coordinatesFromPhysicalFibre field axis transverse))
      (sym (physicalNormMatchesGenerated field axis transverse))
      (pathPoincare (coordinatesFromPhysicalFibre field axis transverse)))

generatedPhysicalFibreMatchLevel : ProofLevel
generatedPhysicalFibreMatchLevel = machineChecked

generatedPhysicalFibrePoincareLevel : ProofLevel
generatedPhysicalFibrePoincareLevel = machineChecked
'''


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("length", type=int)
    parser.add_argument("--certificate-module", required=True)
    parser.add_argument("--bridge-module", required=True)
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def main() -> None:
    arguments = parse_args()
    arguments.output.write_text(
        generate_bridge(
            arguments.length,
            arguments.certificate_module,
            arguments.bridge_module,
        ),
        encoding="utf-8",
    )
    print(arguments.output)


if __name__ == "__main__":
    main()
