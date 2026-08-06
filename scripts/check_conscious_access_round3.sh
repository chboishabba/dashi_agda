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
  DASHI/Biology/NaturalGrowthAlgorithmAtlas.agda
  DASHI/Biology/SquareApollonianPackingComparison.agda
  DASHI/Biology/SignedDistanceBooleanGeometry.agda
  DASHI/Biology/HallHybridManifoldTreeCarrier.agda
  DASHI/Biology/VisualPathBraidResidual.agda
  DASHI/Biology/QuantitativeStateDynamics.agda
  DASHI/Biology/SymbolicCompromiseMinimizer.agda
  DASHI/Biology/StableUnconsciousInvariantRegime.agda
  DASHI/Biology/DynamicCoalitionPhaseEmergence.agda
  DASHI/Biology/ConsciousAccessRound3FullBoundary.agda
  DASHI/Biology/ConsciousAccessRound3SourceAtlas.agda
  DASHI/Biology/ConsciousAccessRound3ExtendedSourceAtlas.agda
  DASHI/Biology/ConsciousAccessRound3Regression.agda
  DASHI/Biology/ConsciousAccessRound3ExtendedRegression.agda
  DASHI/Biology/ConsciousAccessRound3CompleteRegression.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound3CompleteRegression.agda

# A stacked continuation can extend the regression surface without changing
# the workflow definition on the parent branch.  Direct round-four checks set
# ROUND4_DISABLE_CASCADE to avoid recursion.
if [[ -f scripts/check_conscious_access_round4.sh \
      && "${ROUND4_DISABLE_CASCADE:-0}" != "1" ]]; then
  ROUND4_SKIP_ROUND3=1 bash scripts/check_conscious_access_round4.sh
fi
