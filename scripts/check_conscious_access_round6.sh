#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_conscious_access_round5.sh

FILES=(
  DASHI/Biology/TernaryVisualMotifSemiconjugacyExact.agda
  DASHI/Biology/TernaryMorphogeneticVisualFieldExact.agda
  DASHI/Biology/TernaryMotifNeuralObservationQuotientExact.agda
  DASHI/Biology/TriadicVisualBraidCrossPollinationExact.agda
  DASHI/Biology/TernaryHallTransitionCoalitionExact.agda
  DASHI/Biology/ConsciousAccessRound6CrossSourceBridge.agda
  DASHI/Biology/ConsciousAccessRound6CrossPollinationRegression.agda
  DASHI/Biology/Everything.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound6CrossPollinationRegression.agda \
  DASHI/Biology/Everything.agda
