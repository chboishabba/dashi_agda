#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_resonant_audit_round11.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNCherevanSobolevScalingDerivationExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanHeatSchrodingerSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanFiniteHeatSchrodingerGapExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFilteredGeometricDepletionSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteRelativeFilterScaleExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteMagnitudeWeightedDirectionExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteNearFieldCoercivityExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteFilteredSurplusAssemblyExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteAdjointLocalizationCancellationExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteFarFieldAnnularGainExact.agda
  DASHI/Physics/Closure/NSTriadKNGrujicLocalizedVorticityCoherenceSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighHighLowProjectedProductChainExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighHighLowNormConversionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighHighLowCriticalAssemblyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighLowDerivativeRatioExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteLowHighSecondMomentBridgeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteComparableFilteredBridgeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTerminalInteractionDepletionTransferExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGeometricDepletionRound12Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoGeometricDepletionRound12Validation.agda
