#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_future_residual_cantor_metastability_round14.sh"
if [[ -x "$BASE_CHECKER" ]]; then
  "$BASE_CHECKER"
fi

FILES=(
  DASHI/Core/FutureEquivalenceCurrentObservationExact.agda
  DASHI/Cognition/PNF/MultiResolutionAttentionFutureSufficiencyExact.agda
  DASHI/Cognition/PNF/LLMCompressionAccessibilityDefectsExact.agda
  DASHI/Cognition/PNF/LLMCantorMultiResolutionBridgeExact.agda
  DASHI/Cognition/PNF/LLMGrokkingLearningFutureExact.agda
  DASHI/Cognition/PNF/GrokkingMeasureStrataExact.agda
  DASHI/Cognition/PNF/GrokkingEquivalenceStrataExact.agda
  DASHI/Cognition/PNF/GrokkingTaskCharacterPhaseExact.agda
  DASHI/Cognition/PNF/LLMStabilitySufficiencySeparationExact.agda
  DASHI/Cognition/PNF/LLMWeightedFutureQuotientExact.agda
  DASHI/Cognition/PNF/LLMWeightedFutureKernelExact.agda
  DASHI/Cognition/PNF/LLMContextWindowTerminalisationExact.agda
  DASHI/Cognition/PNF/LLMResidualHierarchyExact.agda
  DASHI/Cognition/PNF/NeuralProposalEvidenceBoundaryExact.agda
  DASHI/Cognition/PNF/NeuralBottleneckResidualFutureSafetyExact.agda
  DASHI/Cognition/PNF/LSTMForgetGateFutureSafetyExact.agda
  DASHI/Core/StorageRecomputeResidualOptimizationExact.agda
  DASHI/EverythingLLMMultiResolutionRound17.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'futureEquivalentImpliesCurrentObservationEqual' DASHI/Core/FutureEquivalenceCurrentObservationExact.agda

grep -q 'factorizationCertifiesMultiResolutionFutureSufficiency' DASHI/Cognition/PNF/MultiResolutionAttentionFutureSufficiencyExact.agda
grep -q 'csaCompressionRateExact' DASHI/Cognition/PNF/MultiResolutionAttentionFutureSufficiencyExact.agda
grep -q 'hcaCompressionRateExact' DASHI/Cognition/PNF/MultiResolutionAttentionFutureSufficiencyExact.agda

grep -q 'compressionLossIsReal' DASHI/Cognition/PNF/LLMCompressionAccessibilityDefectsExact.agda
grep -q 'accessibilityLossWithoutRepresentationLoss' DASHI/Cognition/PNF/LLMCompressionAccessibilityDefectsExact.agda
grep -q 'multiResolutionCarrierIsFutureSufficient' DASHI/Cognition/PNF/LLMCompressionAccessibilityDefectsExact.agda

grep -q 'canonicalCantorIndexedFutureSafeCompression' DASHI/Cognition/PNF/LLMCantorMultiResolutionBridgeExact.agda
grep -q 'roundThreeRetainedMassStillUnit' DASHI/Cognition/PNF/LLMCantorMultiResolutionBridgeExact.agda

grep -q 'sameTrainingFitDoesNotImplyLearningFutureEquivalence' DASHI/Cognition/PNF/LLMGrokkingLearningFutureExact.agda
grep -q 'progressResidualSeparatesStates' DASHI/Cognition/PNF/LLMGrokkingLearningFutureExact.agda
grep -q 'trainingUnitDoesNotImplyTaskUnit' DASHI/Cognition/PNF/GrokkingMeasureStrataExact.agda
grep -q 'latentMechanismUnitCanPrecedeVisibleTaskUnit' DASHI/Cognition/PNF/GrokkingMeasureStrataExact.agda
grep -q 'learningFutureImpliesTask' DASHI/Cognition/PNF/GrokkingEquivalenceStrataExact.agda
grep -q 'currentTaskEquivalenceDoesNotImplyLearningFuture' DASHI/Cognition/PNF/GrokkingEquivalenceStrataExact.agda
grep -q 'trainingEquivalenceDoesNotImplyTaskEquivalence' DASHI/Cognition/PNF/GrokkingEquivalenceStrataExact.agda
grep -q 'c3CharacterCompositionExact' DASHI/Cognition/PNF/GrokkingTaskCharacterPhaseExact.agda
grep -q 'phaseOnePlusPhaseTwoWrapsToZero' DASHI/Cognition/PNF/GrokkingTaskCharacterPhaseExact.agda

grep -q 'nonExpansiveComposition' DASHI/Cognition/PNF/LLMStabilitySufficiencySeparationExact.agda
grep -q 'stableMapCannotCarryConsumerObservation' DASHI/Cognition/PNF/LLMStabilitySufficiencySeparationExact.agda
grep -q 'exactRepresentationPreservesNonzeroDistance' DASHI/Cognition/PNF/LLMStabilitySufficiencySeparationExact.agda

grep -q 'weightedFutureRefl' DASHI/Cognition/PNF/LLMWeightedFutureQuotientExact.agda
grep -q 'weightedFutureTrans' DASHI/Cognition/PNF/LLMWeightedFutureQuotientExact.agda
grep -q 'exactSummaryCertifiesWeightedFutureSafety' DASHI/Cognition/PNF/LLMWeightedFutureQuotientExact.agda
grep -q 'ApproximateWeightedFutureEquivalent' DASHI/Cognition/PNF/LLMWeightedFutureQuotientExact.agda

grep -q 'sameCurrentKernelDoesNotImplyCanonicalWeightedFutureEquivalence' DASHI/Cognition/PNF/LLMWeightedFutureKernelExact.agda
grep -q 'allDisplayedKernelsHaveWeightTwo' DASHI/Cognition/PNF/LLMWeightedFutureKernelExact.agda
grep -q 'futureNotWithinUnitTolerance' DASHI/Cognition/PNF/LLMWeightedFutureKernelExact.agda

grep -q 'canonicalContextWindowTerminalisation' DASHI/Cognition/PNF/LLMContextWindowTerminalisationExact.agda
grep -q 'reopenContextExact' DASHI/Cognition/PNF/LLMContextWindowTerminalisationExact.agda
grep -q 'computeResidualCollidesAcrossSemanticDifference' DASHI/Cognition/PNF/LLMResidualHierarchyExact.agda
grep -q 'semanticResidualCollidesAcrossProvenanceDifference' DASHI/Cognition/PNF/LLMResidualHierarchyExact.agda
grep -q 'provenanceResidualReopensExact' DASHI/Cognition/PNF/LLMResidualHierarchyExact.agda

grep -q 'proposalToTypePressure' DASHI/Cognition/PNF/NeuralProposalEvidenceBoundaryExact.agda
grep -q 'neuralPressureCannotPromoteOntologyType' DASHI/Cognition/PNF/NeuralProposalEvidenceBoundaryExact.agda
grep -q 'latentEqualityDoesNotImplyFutureSafety' DASHI/Cognition/PNF/NeuralBottleneckResidualFutureSafetyExact.agda
grep -q 'reopenBottleneckWithResidualExact' DASHI/Cognition/PNF/NeuralBottleneckResidualFutureSafetyExact.agda

grep -q 'forgettingCurrentEqualityIsNotFutureSafety' DASHI/Cognition/PNF/LSTMForgetGateFutureSafetyExact.agda
grep -q 'reopenForgetWithMemoryResidualExact' DASHI/Cognition/PNF/LSTMForgetGateFutureSafetyExact.agda
grep -q '10.1162/neco.1997.9.8.1735' DASHI/Cognition/PNF/LSTMForgetGateFutureSafetyExact.agda

grep -q 'checkpointIsOptimalInFiniteFamily' DASHI/Core/StorageRecomputeResidualOptimizationExact.agda
grep -q 'zeroCacheNotCheaperThanCheckpoint' DASHI/Core/StorageRecomputeResidualOptimizationExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingLLMMultiResolutionRound17.agda
else
  echo "agda unavailable: structural/fail-closed round-17 scan completed; no kernel-clean claim"
fi
