#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Biology/PsychedelicVisualOperatorAlgebra.agda
  DASHI/Biology/MorphogeneticVisualGenerator.agda
  DASHI/Biology/RecursiveSpherePerforation.agda
  DASHI/Biology/NestedApertureVisibility.agda
  DASHI/Biology/LogPolarRetinotopyBridge.agda
  DASHI/Biology/VisualMotifTransitionOperator.agda
  DASHI/Biology/PostAcuteVisualAdaptation.agda
  DASHI/Biology/HallOfHallsCoalition.agda
  DASHI/Biology/PsychedelicMorphogeneticGeometryBoundary.agda
  DASHI/Biology/ConsciousAccessRound3SourceAtlas.agda
  DASHI/Biology/ConsciousAccessRound3Regression.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound3Regression.agda
