#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/AdmissibleTransitionHyperfabricExact.agda
  DASHI/Core/AdmissibleConsumerMDLHyperfabricExact.agda
  DASHI/Chemistry/AdmissibleReactionTransitionBridgeExact.agda
  DASHI/Dynamics/LogisticAdmissibleTransitionBridgeExact.agda
  DASHI/Programmes/RTXAdmissibleConsumerMDLBridgeExact.agda
  DASHI/Environment/LESAdmissibleTransitionMDLCrossPollinationExact.agda
  DASHI/Core/AdmissibleMDLTransitionValidation.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required admissible-MDL source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^data AdmittedStep' DASHI/Core/AdmissibleTransitionHyperfabricExact.agda
grep -q '^disabledExcludesAdmittedStep :' DASHI/Core/AdmissibleTransitionHyperfabricExact.agda
grep -q '^record MinimalEligibleDescription' DASHI/Core/AdmissibleConsumerMDLHyperfabricExact.agda
grep -q '^record ParetoAdmissible' DASHI/Core/AdmissibleConsumerMDLHyperfabricExact.agda
grep -q '^counterexampleExcludesEligibility :' DASHI/Core/AdmissibleConsumerMDLHyperfabricExact.agda
grep -q '^repairStaysInDeclaredNeighbourhood :' DASHI/Core/AdmissibleConsumerMDLHyperfabricExact.agda
grep -q '^reactionTransitionSystem :' DASHI/Chemistry/AdmissibleReactionTransitionBridgeExact.agda
grep -q '^reactionEnablementMDLProblem :' DASHI/Chemistry/AdmissibleReactionTransitionBridgeExact.agda
grep -q '^logisticInvariantRegionAsTransitionSystem :' DASHI/Dynamics/LogisticAdmissibleTransitionBridgeExact.agda
grep -q '^rtxRefinementPreservesConsumerAdequacy :' DASHI/Programmes/RTXAdmissibleConsumerMDLBridgeExact.agda
grep -q '^soilProcessMDLProblem :' DASHI/Environment/LESAdmissibleTransitionMDLCrossPollinationExact.agda

scripts/run_agda29_parallel_check.sh DASHI/Core/AdmissibleMDLTransitionValidation.agda
