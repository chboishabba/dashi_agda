#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Round five is stacked on the complete round-four p-adic reasoning-field lane.
if [[ "${ROUND5_SKIP_ROUND4:-0}" != "1" ]]; then
  ROUND5_DISABLE_CASCADE=1 bash scripts/check_conscious_access_round4.sh
fi

FILES=(
  DASHI/Biology/DASHIYijingTernaryDivinationExact.agda
  DASHI/Biology/OrientedZeroWaveTransitionExact.agda
  DASHI/Biology/DialecticalSheetSpiralExact.agda
  DASHI/Biology/TernaryHypercubeHyperfabricExact.agda
  DASHI/Biology/TernaryMonsterSymmetryCandidateExact.agda
  DASHI/Biology/FRACTRANSSPTransitionExact.agda
  DASHI/Biology/SpectralGrokkingLatticeExact.agda
  DASHI/Biology/ClassicalQuantumLikeCoarseGrainingExact.agda
  DASHI/Biology/AssociativeDivinationPNFExact.agda
  DASHI/Biology/NaturalSystemsHyperfabricExact.agda
  DASHI/Biology/NeuralRepresentationLaplacianExact.agda
  DASHI/Biology/NSYMDialecticalFieldBridgeExact.agda
  DASHI/Biology/DASHIQuantumLikeEntropyOscillatorExact.agda
  DASHI/Biology/ConsciousAccessRound5SourceAtlas.agda
  DASHI/Biology/ConsciousAccessRound5FullBoundary.agda
  DASHI/Biology/ConsciousAccessRound5Regression.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound5Regression.agda
