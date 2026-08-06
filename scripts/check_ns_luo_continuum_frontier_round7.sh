#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_terminal_geometry_round6.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEightPointTorusHaarExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEightPointHaarBochnerExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteBochnerFubiniExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteRationalStepBochnerIntegralExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEightPointIncrementMultiplierExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteLittlewoodPaleyMomentIdentificationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNearWindowScalingObstructionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCutoffTimeDiagonalNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCutoffTimeUniformModulusExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteArbitraryPolynomialAbsorptionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEightPointHeatSemigroupExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFractionalDissipationConventionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHypodissipativeParabolicWindowGapExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWavevectorProjectiveLoopExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteBoundaryLayerVorticityTiltExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteParitySymmetryExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFourResidueSummabilityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteBKMProxyClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoContinuumFrontierRound7Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoContinuumFrontierRound7Validation.agda
