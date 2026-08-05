#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Round four is stacked on the complete round-three visual/morphogenetic lane.
bash scripts/check_conscious_access_round3.sh

FILES=(
  DASHI/Biology/TriadicKernelLiftQuotientExact.agda
  DASHI/Biology/TriadicCarryResidualExact.agda
  DASHI/Biology/PadicCylinderLODReasoningField.agda
  DASHI/Biology/CausalHierarchicalChartResidualExact.agda
  DASHI/Biology/FiniteCrystallisationModeSelectionExact.agda
  DASHI/Biology/FiniteWaveShellGradientExact.agda
  DASHI/Biology/FiniteSymmetryStabiliserExact.agda
  DASHI/Biology/FinitePadicCollapseExact.agda
  DASHI/Biology/ResourceLimitedCrystallisationExact.agda
  DASHI/Biology/ReasoningFieldRenderBridgeExact.agda
  DASHI/Biology/PadicCrystallisationResidueExact.agda
  DASHI/Biology/CoupledWaveTriadicOrderExact.agda
  DASHI/Biology/QuasiperiodicInternalSpaceBoundaryExact.agda
  DASHI/Biology/ConsciousAccessRound4SourceAtlas.agda
  DASHI/Biology/ConsciousAccessRound4FullBoundary.agda
  DASHI/Biology/ConsciousAccessRound4Regression.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound4Regression.agda
