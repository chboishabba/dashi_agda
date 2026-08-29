#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_conscious_access_round6.sh

FILES=(
  DASHI/Biology/TernaryCanonicalOrientationExact.agda
  DASHI/Biology/TernaryFixedTransverseFiniteExact.agda
  DASHI/Biology/TernaryRotationReflectionSeparationExact.agda
  DASHI/Biology/NondegenerateObserverAdmissionExact.agda
  DASHI/Biology/NeuralFixedTransverseObserverBridgeExact.agda
  DASHI/Biology/CyclotomicPhaseAmplitudeBoundaryExact.agda
  DASHI/Biology/EqualCardinalityStructureBoundaryExact.agda
  DASHI/Biology/OggTernaryEquivariantLabellingNoGoExact.agda
  DASHI/Biology/OperatorStructureAdmissionBoundaryExact.agda
  DASHI/Biology/ConsciousAccessRound7AristotleSourceBridge.agda
  DASHI/Biology/ConsciousAccessRound7AristotleRegression.agda
  DASHI/Biology/Everything.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound7AristotleRegression.agda \
  DASHI/Biology/Everything.agda
