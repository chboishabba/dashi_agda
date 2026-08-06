#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Round five is stacked on the complete round-four p-adic reasoning-field lane.
if [[ "${ROUND5_SKIP_ROUND4:-0}" != "1" ]]; then
  if [[ "${ROUND5_DISABLE_CASCADE:-0}" == "1" ]]; then
    ROUND4_SKIP_ROUND3=1 bash scripts/check_conscious_access_round4.sh
  else
    bash scripts/check_conscious_access_round4.sh
  fi
fi

FILES=(
  DASHI/Biology/DASHIYijingTernaryDivinationExact.agda
  DASHI/Biology/DASHIYijingRelationalOperatorsExact.agda
  DASHI/Biology/OrientedZeroWaveTransitionExact.agda
  DASHI/Biology/DialecticalSheetSpiralExact.agda
  DASHI/Biology/TriadicBraidDialecticExact.agda
  DASHI/Biology/TernaryHypercubeHyperfabricExact.agda
  DASHI/Biology/TernaryCubeStrataExact.agda
  DASHI/Biology/TernaryCantorWheelDiffusionExact.agda
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
  DASHI/Biology/ConsciousAccessRound5ExtendedSourceAtlas.agda
  DASHI/Biology/ConsciousAccessRound5FullBoundary.agda
  DASHI/Biology/ConsciousAccessRound5Regression.agda
  DASHI/Biology/ReducedFiftyThreeFibreExact.agda
  DASHI/Biology/SignedSSPFRACTRANWeaveExact.agda
  DASHI/Biology/SSPHyperfibreSymmetryTowerExact.agda
  DASHI/Biology/SelfIndexingHyperfabricTetrationExact.agda
  DASHI/Biology/EquivariantLaplacianSectorExact.agda
  DASHI/Biology/D4IrrepPhysicalRoleExact.agda
  DASHI/Biology/OrientedZeroJetTransitionExact.agda
  DASHI/Biology/ReachableSectorEntropyExact.agda
  DASHI/Biology/ExceptionalLatticeGrokkingProtocolExact.agda
  DASHI/Biology/MoonshineGradedStageBridgeExact.agda
  DASHI/Biology/ClayCrossPollinationInterfaceExact.agda
  DASHI/Biology/ConsciousAccessRound5CompletionSourceAtlas.agda
  DASHI/Biology/ConsciousAccessRound5CompletionBoundary.agda
  DASHI/Biology/ConsciousAccessRound5CompletionRegression.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required round-five source is missing: $file" >&2
    exit 1
  fi

  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound5Regression.agda \
  DASHI/Biology/ConsciousAccessRound5CompletionRegression.agda \
  DASHI/Biology/Everything.agda
