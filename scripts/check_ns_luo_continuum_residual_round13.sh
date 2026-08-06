#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_geometric_depletion_round12.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNLuoFinitePeriodicLerayDivergenceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePeriodicBernsteinSupportExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTensorHolderExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePeriodicHighHighLowProducerExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePeriodicHighHighLowClosedExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighHighTerminalCauchyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighLowKernelAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighLowCriticalKernelDominationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoLowHighExponentClassificationExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteAnnularReassignmentScaleExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteAnnularCarlesonEndpointExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteWeightedCommutatorInsertionExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteLocalizationAbsorptionExact.agda
  DASHI/Physics/Closure/NSTriadKNYuFiniteSurplusVanishingTransferExact.agda
  DASHI/Physics/Closure/NSTriadKNYuResidualClosureSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNGrujicLinearSparsenessExact.agda
  DASHI/Physics/Closure/NSTriadKNGrujicLogarithmicDepletionSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoContinuumResidualRound13Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoContinuumResidualRound13Validation.agda
