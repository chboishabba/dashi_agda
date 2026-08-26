#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Foundations/WetteArithmeticRepresentationExact.agda
  DASHI/Foundations/WetteConstructiveAutomatonExact.agda
  DASHI/Foundations/WetteArithmeticTransitionBridgeExact.agda
  DASHI/Foundations/WetteFiniteDeductionTraceExact.agda
  DASHI/Foundations/WetteFiniteDerivationCompositionExact.agda
  DASHI/Foundations/WetteFiniteCalculusTranslationExact.agda
  DASHI/Foundations/WetteRepresentationKernelBridgeExact.agda
  DASHI/Foundations/WetteCertifiedArithmeticKernelExact.agda
  DASHI/Foundations/WetteFRACTRANCrossPollinationExact.agda
  DASHI/Foundations/WetteBernaysConsistencyDeductionBoundaryExact.agda
  DASHI/Foundations/WetteFiniteDerivabilityBernaysBridgeExact.agda
  DASHI/Foundations/WetteFiniteTraceConsistencyObstructionExact.agda
  DASHI/Foundations/WetteConsistencyClaimBoundaryExact.agda
  DASHI/Foundations/Wette/Everything.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required Wette reconstruction source is missing: $file" >&2
    exit 1
  fi

  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

# Promotion-boundary guards.
grep -q 'historicalWetteCodecRecoveredIsFalse' \
  DASHI/Foundations/WetteArithmeticRepresentationExact.agda
grep -q 'fractranMachineIsHistoricalWetteMachineIsFalse' \
  DASHI/Foundations/WetteFRACTRANCrossPollinationExact.agda
grep -q 'ordinaryArithmeticInconsistencyEstablishedIsFalse' \
  DASHI/Foundations/WetteBernaysConsistencyDeductionBoundaryExact.agda
grep -q 'machineReachabilityIsAlreadyMetatheoreticContradictionIsFalse' \
  DASHI/Foundations/WetteFiniteDerivabilityBernaysBridgeExact.agda
grep -q 'theoremProvesOrdinaryArithmeticConsistencyIsFalse' \
  DASHI/Foundations/WetteFiniteTraceConsistencyObstructionExact.agda
grep -q 'historicalWetteToOrdinaryArithmeticTranslationRecoveredIsFalse' \
  DASHI/Foundations/WetteFiniteCalculusTranslationExact.agda
grep -q 'historicalWetteOrdinaryArithmeticEquiconsistencyRecoveredIsFalse' \
  DASHI/Foundations/WetteConsistencyClaimBoundaryExact.agda
grep -q 'contradictionInOrdinaryArithmeticProvedIsFalse' \
  DASHI/Foundations/WetteConsistencyClaimBoundaryExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/WetteFiniteDeductionTraceExact.agda \
  DASHI/Foundations/WetteFiniteDerivationCompositionExact.agda \
  DASHI/Foundations/WetteFiniteCalculusTranslationExact.agda \
  DASHI/Foundations/WetteFiniteDerivabilityBernaysBridgeExact.agda \
  DASHI/Foundations/WetteFiniteTraceConsistencyObstructionExact.agda \
  DASHI/Foundations/Wette/Everything.agda
