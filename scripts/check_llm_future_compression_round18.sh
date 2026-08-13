#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_llm_multires_future_sufficiency_round17.sh"
if [[ -f "$BASE_CHECKER" ]]; then
  bash "$BASE_CHECKER"
fi

FILES=(
  DASHI/Cognition/PNF/RationalProbabilityFutureKernelExact.agda
  DASHI/Cognition/PNF/RationalProbabilityFutureQuotientExact.agda
  DASHI/Core/FiniteFuturePartitionRefinementExact.agda
  DASHI/Core/FiniteFuturePartitionCanonicalBridgeExact.agda
  DASHI/Core/ResidualFibreLowerBoundExact.agda
  DASHI/Core/ResidualBitLowerBoundThreeExact.agda
  DASHI/Cognition/PNF/ModularFourierGrokkingC3Exact.agda
  DASHI/Cognition/PNF/GrokkingCantorRefinementExact.agda
  DASHI/Cognition/PNF/DynamicMultiQueryMultiResolutionExact.agda
  DASHI/Core/ResidualObligationLatticeExact.agda
  DASHI/Cognition/PNF/LearningProvenanceFutureExact.agda
  DASHI/Cognition/PNF/OpticalTextCompressionPNFExact.agda
  DASHI/Cognition/PNF/MultimodalPhaseFutureEquivalenceExact.agda
  DASHI/Cognition/PNF/MultimodalPNFPhaseOrthogonalityExact.agda
  DASHI/Foundations/CantorProjectiveCylinderMeasureExact.agda
  DASHI/EverythingLLMFutureCompressionRound18.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'totalVariationTriangle' DASHI/Cognition/PNF/RationalProbabilityFutureKernelExact.agda
grep -q 'approxFutureErrorComposition' DASHI/Cognition/PNF/RationalProbabilityFutureKernelExact.agda
grep -q 'probabilityDataProcessing' DASHI/Cognition/PNF/RationalProbabilityFutureKernelExact.agda
grep -q 'probabilityFutureTrans' DASHI/Cognition/PNF/RationalProbabilityFutureQuotientExact.agda
grep -q 'exactSummaryCertifiesProbabilityFutureSafety' DASHI/Cognition/PNF/RationalProbabilityFutureQuotientExact.agda
grep -q 'safeProjectionToleranceMonotone' DASHI/Cognition/PNF/RationalProbabilityFutureQuotientExact.agda

grep -q 'depthEquivalentMonotone' DASHI/Core/FiniteFuturePartitionRefinementExact.agda
grep -q 'stableRefinementIsFutureSafe' DASHI/Core/FiniteFuturePartitionRefinementExact.agda
grep -q 'stableRefinementPresentation' DASHI/Core/FiniteFuturePartitionCanonicalBridgeExact.agda
grep -q 'canonicalFutureEquivalentImpliesStableCodeEquality' DASHI/Core/FiniteFuturePartitionCanonicalBridgeExact.agda

grep -q 'exactResidualInjectiveOnEveryFibre' DASHI/Core/ResidualFibreLowerBoundExact.agda
grep -q 'distinctFutureClassesForceDistinctResiduals' DASHI/Core/ResidualFibreLowerBoundExact.agda
grep -q 'threeStateFibreRequiresThreeDistinctResidualCodes' DASHI/Core/ResidualFibreLowerBoundExact.agda

grep -q 'oneBitCannotExactlyReopenThreeStateFibre' DASHI/Core/ResidualBitLowerBoundThreeExact.agda
grep -q 'twoBitsReopenThreeStateFibreExactly' DASHI/Core/ResidualBitLowerBoundThreeExact.agda

grep -q 'memorizerFitsEveryTrainingPair' DASHI/Cognition/PNF/ModularFourierGrokkingC3Exact.agda
grep -q 'memorizerAndAlgorithmNotFullTaskEquivalent' DASHI/Cognition/PNF/ModularFourierGrokkingC3Exact.agda
grep -q 'algorithmicRuleIsCharacterComposition' DASHI/Cognition/PNF/ModularFourierGrokkingC3Exact.agda

grep -q 'compressionAndGeneralizationCanMoveTogether' DASHI/Cognition/PNF/GrokkingCantorRefinementExact.agda
grep -q 'cantorLayerRemainsUnitAtEveryLearningStage' DASHI/Cognition/PNF/GrokkingCantorRefinementExact.agda

grep -q 'compressCommutesWithEveryQueryTrace' DASHI/Cognition/PNF/DynamicMultiQueryMultiResolutionExact.agda
grep -q 'sameInitialRetainedCarrierImpliesSameObservationAfterEveryQueryTrace' DASHI/Cognition/PNF/DynamicMultiQueryMultiResolutionExact.agda

grep -q 'strongResidualAlsoSatisfiesWeakerObligation' DASHI/Core/ResidualObligationLatticeExact.agda
grep -q 'strictlyStrongerObligationForcesResidualDistinction' DASHI/Core/ResidualObligationLatticeExact.agda

grep -q 'sameParameterStateHasDifferentLearningFuture' DASHI/Cognition/PNF/LearningProvenanceFutureExact.agda

grep -q 'perfectSurfaceReconstructionDoesNotImplyFineFutureSafety' DASHI/Cognition/PNF/OpticalTextCompressionPNFExact.agda
grep -q 'reopenOpticalWithProvenanceExact' DASHI/Cognition/PNF/OpticalTextCompressionPNFExact.agda
grep -q '10.18653/v1/2025.findings-emnlp.558' DASHI/Cognition/PNF/OpticalTextCompressionPNFExact.agda
grep -q '10.48550/arXiv.2510.18234' DASHI/Cognition/PNF/OpticalTextCompressionPNFExact.agda

grep -q 'modalityChangeCommutesWithTaskPhaseAdvance' DASHI/Cognition/PNF/MultimodalPhaseFutureEquivalenceExact.agda
grep -q 'sameLatentImpliesCrossModalConsumerEquivalence' DASHI/Cognition/PNF/MultimodalPhaseFutureEquivalenceExact.agda
grep -q 'modalityReencodingPreservesSemanticPhase' DASHI/Cognition/PNF/MultimodalPNFPhaseOrthogonalityExact.agda
grep -q 'semanticPhaseChangesWithoutModalityChange' DASHI/Cognition/PNF/MultimodalPNFPhaseOrthogonalityExact.agda

grep -q 'parentMassSplitsExactly' DASHI/Foundations/CantorProjectiveCylinderMeasureExact.agda
grep -q 'canonicalPolarCylinderPremeasure' DASHI/Foundations/CantorProjectiveCylinderMeasureExact.agda
grep -q 'embeddedStreamIsPolar' DASHI/Foundations/CantorProjectiveCylinderMeasureExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingLLMFutureCompressionRound18.agda
else
  echo "agda unavailable: structural/fail-closed round-18 scan completed; no kernel-clean claim"
fi
