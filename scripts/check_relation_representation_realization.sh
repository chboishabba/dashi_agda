#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
  DASHI/Reasoning/RelationRepresentationAdequacyExact.agda
  DASHI/Reasoning/RelationRepresentationRealizationExact.agda
  DASHI/Reasoning/BidirectionalRelationRepresentationBridgeExact.agda
  DASHI/Reasoning/RelationRepresentationExperimentProtocolExact.agda
  DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
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

grep -q '10.52202/085713-1438' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2510.09790' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2605.05115' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2602.05266' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2509.19323' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2601.16907' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2606.01402' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
grep -q '10.48550/arXiv.2602.02859' DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda

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

grep -q 'functioningDoesNotRecoverCapability' DASHI/Reasoning/EigenslurFlourishingRelationBoundaryExact.agda
grep -q 'oneHumourConsumerSafetyDoesNotEstablishPluralSafety' DASHI/Reasoning/HumourRelationRepresentationCrossPollinationExact.agda
grep -q 'neuralSearchMayReopenFromOffsetToRotation' DASHI/Reasoning/NeuralSpectralRelationCrossPollinationExact.agda
grep -q 'grokkingCurrentFitDoesNotCloseLearningFuture' DASHI/Reasoning/RelationRepresentationCrossPollinationExact.agda
grep -q 'finiteDifferenceSensitivityIsStateDependent' DASHI/Reasoning/RelationRepresentationRegression.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
  agda -i . -i src DASHI/Reasoning/RelationRepresentationRegression.agda
  agda -i . -i src DASHI/Reasoning/Everything.agda
else
  echo "agda unavailable: structural/fail-closed relation-representation scan completed; no kernel-clean claim"
fi
