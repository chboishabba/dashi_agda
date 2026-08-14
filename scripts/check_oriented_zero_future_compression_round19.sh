#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_llm_future_compression_round18.sh"
if [[ -f "$BASE_CHECKER" ]]; then
  bash "$BASE_CHECKER"
fi

FILES=(
  DASHI/Cognition/PNF/OrientedZeroFutureQuotientExact.agda
  DASHI/Cognition/PNF/OrientedZeroCanonicalFutureExact.agda
  DASHI/Cognition/PNF/OrientedZeroPartitionRefinementExact.agda
  DASHI/Cognition/PNF/OrientedZeroBitMinimalityExact.agda
  DASHI/Cognition/PNF/OrientedZeroGrayTransitionGeometryExact.agda
  DASHI/Cognition/PNF/OrientedZeroPhaseOrthogonalityExact.agda
  DASHI/Cognition/PNF/FutureRateDistortionOrientedZeroExact.agda
  DASHI/Cognition/PNF/FutureRateDistortionGenericExact.agda
  DASHI/Core/GeneralResidualFibreCardinalityExact.agda
  DASHI/Core/GenericFuturePartitionRefinementExact.agda
  DASHI/Core/FiniteRankedRefinementStabilizationExact.agda
  DASHI/Cognition/PNF/ApproximateMultimodalFutureEquivalenceExact.agda
  DASHI/Cognition/PNF/DynamicApproximateMultiResolutionErrorExact.agda
  DASHI/Cognition/PNF/SpectralGrokkingPhaseDynamicsExact.agda
  DASHI/Cognition/PNF/FullLearningStateFutureQuotientExact.agda
  DASHI/EverythingOrientedZeroFutureCompressionRound19.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'zeroFibreSplitsUnderFutureRefinement' DASHI/Cognition/PNF/OrientedZeroFutureQuotientExact.agda
grep -q 'adaptiveResidualReopensExactly' DASHI/Cognition/PNF/OrientedZeroFutureQuotientExact.agda
grep -q 'negativeZeroNotCanonicalFutureEquivalentPositiveZero' DASHI/Cognition/PNF/OrientedZeroCanonicalFutureExact.agda
grep -q 'zeroPairSeparatedAtDepthOne' DASHI/Cognition/PNF/OrientedZeroPartitionRefinementExact.agda
grep -q 'oneBitCannotEncodeFourWaveStatesExactly' DASHI/Cognition/PNF/OrientedZeroBitMinimalityExact.agda
grep -q 'scalarPlusOneBitReopensExactly' DASHI/Cognition/PNF/OrientedZeroBitMinimalityExact.agda
grep -q 'grayStrictlyImprovesPathDistortion' DASHI/Cognition/PNF/OrientedZeroGrayTransitionGeometryExact.agda
grep -q 'orientationAndProcessAdvanceCommute' DASHI/Cognition/PNF/OrientedZeroPhaseOrthogonalityExact.agda

grep -q 'orientedResidualIsZeroDistortionOptimal' DASHI/Cognition/PNF/FutureRateDistortionOrientedZeroExact.agda
grep -q 'optimalRateAntitoneInTolerance' DASHI/Cognition/PNF/FutureRateDistortionGenericExact.agda
grep -q 'zeroDistortionOptimumIsSafe' DASHI/Cognition/PNF/FutureRateDistortionGenericExact.agda

grep -q 'residualInjectionFromFutureDistinctFibre' DASHI/Core/GeneralResidualFibreCardinalityExact.agda
grep -q 'futureSafetyForBitWordsImpliesCapacityBound' DASHI/Core/GeneralResidualFibreCardinalityExact.agda
grep -q 'refinementMonotone' DASHI/Core/GenericFuturePartitionRefinementExact.agda
grep -q 'stablePersists' DASHI/Core/GenericFuturePartitionRefinementExact.agda
grep -q 'rankedRefinementStabilizes' DASHI/Core/FiniteRankedRefinementStabilizationExact.agda

grep -q 'crossModalFutureDistortionBound' DASHI/Cognition/PNF/ApproximateMultimodalFutureEquivalenceExact.agda
grep -q 'traceErrorBound' DASHI/Cognition/PNF/DynamicApproximateMultiResolutionErrorExact.agda
grep -q 'characterAmplitudeRisesBeforeBehaviorMoves' DASHI/Cognition/PNF/SpectralGrokkingPhaseDynamicsExact.agda
grep -q 'equalZeroGainDoesNotDetermineLearningFuture' DASHI/Cognition/PNF/SpectralGrokkingPhaseDynamicsExact.agda
grep -q 'sameBatchDifferentLearningFuture' DASHI/Cognition/PNF/FullLearningStateFutureQuotientExact.agda
grep -q 'learningResidualReopensExact' DASHI/Cognition/PNF/FullLearningStateFutureQuotientExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingOrientedZeroFutureCompressionRound19.agda
else
  echo "agda unavailable: structural/fail-closed round-19 scan completed; no kernel-clean claim"
fi
