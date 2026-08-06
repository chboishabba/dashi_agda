#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_commutator_continuum_round14.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNDaLioRiviereThreeTermCommutatorSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNFrankSukochevZaninCommutatorSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicWalshCharacterOrthogonalityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicWalshParsevalExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicGalerkinParsevalExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicGalerkinSupportUniformExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicGalerkinHighHighTerminalExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicCenteredKernelSecondMomentExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEightPointSixThreeHolderExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeKernelEstimateExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoLowHighSixThreeTerminalExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighLowDerivativePlacementTerminalExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteFarFieldConvolutionC0Exact.agda
  DASHI/Physics/Closure/NSTriadKNYuIncrementDefectCriticalKernelExact.agda
  DASHI/Physics/Closure/NSTriadKNYuLocalizationCaccioppoliTailExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicGalerkinFourClassContinuationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinUniformLimitContinuationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDirectionalDefectGramExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBadCoherenceDynamicRarityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBadCoherenceWeightedMarkovExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBadCoherenceWeightedDefectTransferExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGoodCoherenceWeightedDefectExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinKernelRound15Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)|\b(TODO|FIXME|placeholder)\b' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinKernelRound15Validation.agda
