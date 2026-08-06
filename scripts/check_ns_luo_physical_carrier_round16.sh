#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_galerkin_kernel_round15.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNLuoLowHighExponentBookkeepingCorrectedExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeHolderConstantOneV2Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeHolderDimensionFreeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeKernelDimensionFreeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCenteredDifferenceSixThreeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoIntegerCubeSupportCapacityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoConcreteIntegerCube125EnumerationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoConcreteDyadicSupportCount125Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoConcreteBernstein125Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGrowingFiniteCubeSupportExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGrowingDyadicAnnulusExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGrowingCubeBernsteinExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGrowingDyadicAnnulusBernsteinExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGrowingCubeHighHighClosedExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGrowingCubeHighHighTensorClosedExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGrowingDyadicAnnulusHighHighExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGrowingDyadicAnnulusHighHighTerminalExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoAnnularFourClassContinuationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteRootOfUnityCancellationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoThreeDimensionalCharacterOrthogonalityFactorExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteKroneckerEnumerationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFinEnumerationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFourierParsevalFromInversionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFourierInversionFromResolutionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFourierFromUniqueResolutionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFourierRestrictionContractiveExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteModeRestrictionContractiveExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinInteractionDifferenceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinTensorDifferenceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinDiagonalSelectionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalCarrierRound16Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)|\b(TODO|FIXME|placeholder)\b' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalCarrierRound16Validation.agda
