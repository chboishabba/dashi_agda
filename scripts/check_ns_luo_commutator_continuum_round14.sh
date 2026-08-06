#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_continuum_residual_round13.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDyadicSupportCountExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFourierCoefficientL1Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDyadicBernsteinRealizationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteParsevalExtractionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoRationalLerayMultiplierContractiveExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoRound14FinitePeriodicHighHighClosedExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoRound14FinitePeriodicHighHighTensorClosedExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCenteredPairedCommutatorIdentityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSixThreeCenteredCommutatorScaleExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeCommutatorBudgetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighLowTerminalClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNYuExteriorTailCriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNYuIncrementDefectTailCriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNYuLocalizationTailCriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNYuResidualJointTailClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoRound14SquaredFourClassClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNDAnconaCommutatorSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNHessChildsTransportCommutatorSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNTaoLocalWellPosednessContinuationInterfaceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCommutatorContinuumRound14Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoCommutatorContinuumRound14Validation.agda
