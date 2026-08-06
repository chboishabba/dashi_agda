#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Round five is stacked on the complete Round Four p-adic/crystallisation lane.
if [[ "${ROUND5_SKIP_ROUND4:-0}" != "1" ]]; then
  bash scripts/check_conscious_access_round4.sh
fi

FILES=(
  DASHI/Physics/Foundations/ParameterScaleTaxonomyExact.agda
  DASHI/Physics/Foundations/ParameterInformationGeometryExact.agda
  DASHI/Physics/Foundations/RGMDLExhaustionChambersExact.agda
  DASHI/Physics/Foundations/DimensionPowerCountingBoundaryExact.agda
  DASHI/Physics/Foundations/AtomicFermionShellExact.agda
  DASHI/Physics/Foundations/AtomicValenceFermionBridgeExact.agda
  DASHI/Physics/Foundations/NuclearShellPairingExact.agda
  DASHI/Physics/Foundations/NuclearShapeInstabilityExact.agda
  DASHI/Physics/Foundations/CausalCodingCosmologyBoundaryExact.agda
  DASHI/Physics/Foundations/KernelGeometryEmergenceObligations.agda
  DASHI/Physics/Foundations/FiniteGraphGaugeScalarExact.agda
  DASHI/Physics/Foundations/KernelQFTEmergenceObligations.agda
  DASHI/Physics/Foundations/UnifiedEffectiveActionBoundary.agda
  DASHI/Physics/Foundations/Round5SourceAtlas.agda
  DASHI/Physics/Foundations/Round5FullBoundary.agda
  DASHI/Physics/Foundations/Round5Regression.agda
  DASHI/Physics/Foundations/Everything.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/Round5Regression.agda
