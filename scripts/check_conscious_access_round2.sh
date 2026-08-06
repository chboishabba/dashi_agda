#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Biology/QuantitativeCompositionalDefect.agda
  DASHI/Biology/DynamicEffectiveTopology.agda
  DASHI/Biology/FiniteCoalitionConstruction.agda
  DASHI/Biology/ConsciousAccessRound2SourceAtlas.agda
  DASHI/Biology/ConsciousAccessRound2Regression.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound2Regression.agda
