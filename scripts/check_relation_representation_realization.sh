#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
  DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
  DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
  DASHI/Reasoning/RelationRepresentationAdequacyExact.agda
  DASHI/Reasoning/RelationRepresentationRealizationExact.agda
  DASHI/Reasoning/BidirectionalRelationRepresentationBridgeExact.agda
  DASHI/Reasoning/RelationRepresentationExperimentProtocolExact.agda
  DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
  DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda
  DASHI/Reasoning/EigenslurFlourishingRelationBoundaryExact.agda
  DASHI/Reasoning/RelationRepresentationCrossPollinationExact.agda
  DASHI/Reasoning/HumourRelationRepresentationCrossPollinationExact.agda
  DASHI/Reasoning/NeuralSpectralRelationCrossPollinationExact.agda
  DASHI/Reasoning/RelationRepresentationRegression.agda
  DASHI/Reasoning/Everything.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

test -s scripts/relation_representation_numeric_producer.py
test -s Artifacts/relation-representation/numeric-producer-receipt.json
python3 scripts/relation_representation_numeric_producer.py

grep -q 'dashi.relation-representation.numeric-producer.v1' Artifacts/relation-representation/numeric-producer-receipt.json
grep -q '"spectral_gap": 8' Artifacts/relation-representation/numeric-producer-receipt.json
grep -q '"singular_values"' Artifacts/relation-representation/numeric-producer-receipt.json
grep -q '"reconstruction_error": 0' Artifacts/relation-representation/numeric-producer-receipt.json
grep -q '"squared_error": 0' Artifacts/relation-representation/numeric-producer-receipt.json
grep -q '"state_dependent": true' Artifacts/relation-representation/numeric-producer-receipt.json

grep -q '10.52202/085713-1438' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2510.09790' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2605.05115' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2602.05266' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2509.19323' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2601.16907' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2606.01402' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2602.02859' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda

grep -q 'christRelationDecoderValidation' DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
grep -q 'riseRotationValidation' DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
grep -q 'recosValidation' DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
grep -q 'magnitudeAwareValidation' DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
grep -q 'calibratedSimilarityValidation' DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
grep -q 'manifoldSteeringValidation' DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
grep -q 'differentialEquivalenceValidation' DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
grep -q 'currentExternalStudyPayloadAvailability' DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda

grep -q 'evidenceFibreStage' DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
grep -q 'predictionEnvelopeStage' DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
grep -q 'calibratedInferenceStage' DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
grep -q 'certifiedSensitivityStage' DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
grep -q 'robustnessDiscrepancyStage' DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
grep -q 'heldOutValidationStage' DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
grep -q 'stage67OwnersShouldBeReusedAfterMerge' DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda

grep -q 'sameRetainedRelationStateGivesSameObservationAfterEveryTrace' DASHI/Reasoning/RelationRepresentationAdequacyExact.agda
grep -q 'RepresentationRealizationWitness' DASHI/Reasoning/RelationRepresentationRealizationExact.agda
grep -q 'collisionReopensBidirectionalCut' DASHI/Reasoning/BidirectionalRelationRepresentationBridgeExact.agda
grep -q 'ReopenedCandidateSearch' DASHI/Reasoning/RelationRepresentationExperimentProtocolExact.agda

grep -q '10.1017/CBO9781139020411' DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
grep -q 'principalEigenpair' DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
grep -q 'rankOneOuterProductReceipt' DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
grep -q 'mismatchRankOneObstruction' DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
grep -q 'quarterTurnFourth' DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
grep -q 'affineDemoAt23' DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
grep -q 'localSensitivityChangesWithState' DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
grep -q 'ManifoldProducerObligation' DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda

grep -q 'ExactSVD2' DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda
grep -q 'canonicalSampleSVD' DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda
grep -q 'principalSingularScaleSquaresToGramEigenvalue' DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda
grep -q 'ExternalNumericalReceiptContract' DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda
grep -q 'JacobianProducerObligation' DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda
grep -q 'finiteDifferencePreJacobianWitness' DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda

grep -q 'functioningDoesNotRecoverCapability' DASHI/Reasoning/EigenslurFlourishingRelationBoundaryExact.agda
grep -q 'oneHumourConsumerSafetyDoesNotEstablishPluralSafety' DASHI/Reasoning/HumourRelationRepresentationCrossPollinationExact.agda
grep -q 'neuralSearchMayReopenFromOffsetToRotation' DASHI/Reasoning/NeuralSpectralRelationCrossPollinationExact.agda
grep -q 'grokkingCurrentFitDoesNotCloseLearningFuture' DASHI/Reasoning/RelationRepresentationCrossPollinationExact.agda
grep -q 'principalSVDReceipt' DASHI/Reasoning/RelationRepresentationRegression.agda
grep -q 'externalFixtureDoesNotClaimEmpiricalEmbeddings' DASHI/Reasoning/RelationRepresentationRegression.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
  agda -i . -i src DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
  agda -i . -i src DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
  agda -i . -i src DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda
  agda -i . -i src DASHI/Reasoning/RelationRepresentationRegression.agda
  agda -i . -i src DASHI/Reasoning/Everything.agda
else
  echo "agda unavailable: structural/fail-closed relation-representation scan completed; no kernel-clean claim"
fi
