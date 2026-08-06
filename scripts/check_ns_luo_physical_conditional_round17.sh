#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_physical_carrier_round16.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNLuoTorusTrigonometricPolynomialExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTorusTrigonometricParsevalExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTorusFourierDifferentiationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTorusLerayContractiveExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalCenteredCommutatorAssemblyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFourierGalerkinTailExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSobolevTensorProjectionErrorExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalDirectionalDefectExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoIntegratedHighHighResidenceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoInageDirectionalAbsorptionComparisonExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoNonlinearWeakLimitAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalConditionalContinuationRound17Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalConditionalRound17Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)|\b(TODO|FIXME|placeholder)\b' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalConditionalRound17Validation.agda
