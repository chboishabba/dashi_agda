#!/usr/bin/env bash
set -euo pipefail

# The regression root transitively checks the full conscious-access tranche.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Biology/StateDependentMultiplexTransducer.agda
  DASHI/Biology/ProductiveTransformCoherence.agda
  DASHI/Biology/SparseExpertRoutingCoalition.agda
  DASHI/Biology/ConsciousAccessCoalition.agda
  DASHI/Biology/UnconsciousAccessRegime.agda
  DASHI/Biology/SymbolicTransformWithoutHomunculus.agda
  DASHI/Biology/DeterministicCoarseGrainingBoundary.agda
  DASHI/Biology/PsychedelicAttractorReweightingBoundary.agda
  DASHI/Biology/ConsciousAccessNetworkSourceAtlas.agda
  DASHI/Biology/ConsciousAccessNetworkRegression.agda
  DASHI/Biology/Everything.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessNetworkRegression.agda
