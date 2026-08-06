#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# This physics/constants tranche is stacked directly on PR #399.  Validate the
# complete biology/Yijing/natural-system Round Five before checking the added
# foundations surface.
if [[ "${UNIFICATION_ROUND5_SKIP_BIOLOGY:-0}" != "1" ]]; then
  bash scripts/check_conscious_access_round5.sh
fi

FILES=(
  DASHI/Physics/Foundations/ParameterScaleTaxonomyExact.agda
  DASHI/Physics/Foundations/ParameterInformationGeometryExact.agda
  DASHI/Physics/Foundations/ScaleInvariantTheorySelectionExact.agda
  DASHI/Physics/Foundations/PadicCausalChartLosslessExact.agda
  DASHI/Physics/Foundations/ModularProjectionQuantisationExact.agda
  DASHI/Physics/Foundations/RGMDLExhaustionChambersExact.agda
  DASHI/Physics/Foundations/DimensionPowerCountingBoundaryExact.agda
  DASHI/Physics/Foundations/DiscreteLorentzEmergenceBoundaryExact.agda
  DASHI/Physics/Foundations/AtomicFermionShellExact.agda
  DASHI/Physics/Foundations/AtomicValenceFermionBridgeExact.agda
  DASHI/Physics/Foundations/AtomicGenerationPipelineExact.agda
  DASHI/Physics/Foundations/NuclearShellPairingExact.agda
  DASHI/Physics/Foundations/NuclearShapeInstabilityExact.agda
  DASHI/Physics/Foundations/NuclearResponseComplexityExact.agda
  DASHI/Physics/Foundations/CausalCodingCosmologyBoundaryExact.agda
  DASHI/Physics/Foundations/CMBInformationChannelExact.agda
  DASHI/Physics/Foundations/KernelGeometryEmergenceObligations.agda
  DASHI/Physics/Foundations/FiniteStressConservationGeodesicExact.agda
  DASHI/Physics/Foundations/FiniteGraphGaugeScalarExact.agda
  DASHI/Physics/Foundations/FiniteFockExcitationExact.agda
  DASHI/Physics/Foundations/KernelQFTEmergenceObligations.agda
  DASHI/Physics/Foundations/KernelEmergenceHypothesesExact.agda
  DASHI/Physics/Foundations/PR399FoundationsCrossPollinationExact.agda
  DASHI/Physics/Foundations/UnifiedEffectiveActionBoundary.agda
  DASHI/Physics/Foundations/Round5SourceAtlas.agda
  DASHI/Physics/Foundations/Round5CombinedSourceBoundary.agda
  DASHI/Physics/Foundations/Round5CompletionRegression.agda
  DASHI/Physics/Foundations/Round5FullBoundary.agda
  DASHI/Physics/Foundations/Round5Regression.agda
  DASHI/Physics/Foundations/Everything.agda
  DASHI/Unified/Everything.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required unification round-five source is missing: $file" >&2
    exit 1
  fi

  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/Round5Regression.agda \
  DASHI/Physics/Foundations/Everything.agda \
  DASHI/Unified/Everything.agda
