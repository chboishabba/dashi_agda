#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Reasoning/RelationRepresentationSourceRegistryExact.agda
  DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
  DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
  DASHI/Reasoning/RelationRepresentationExternalReceiptAdmissionExact.agda
  DASHI/Reasoning/ImplementationExperimentProvenanceExact.agda
  DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
  DASHI/Reasoning/DASHIgGrokkingStage67SpecimenExact.agda
  DASHI/Reasoning/RelationRepresentationAdequacyExact.agda
  DASHI/Reasoning/RelationRepresentationRealizationExact.agda
  DASHI/Reasoning/BidirectionalRelationRepresentationBridgeExact.agda
  DASHI/Reasoning/RelationRepresentationExperimentProtocolExact.agda
  DASHI/Reasoning/RelationRepresentationCandidateDiscriminationExact.agda
  DASHI/Reasoning/RelationRepresentationMechanismSocketExact.agda
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

python3 scripts/relation_representation_numeric_producer.py
python3 scripts/validate_relation_representation_external_receipt.py --allow-template Artifacts/relation-representation/external-study-receipt-template.json

grep -q '013962fb839e83ce8e4b35486fe1a79792c96db8' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q 'leech022T50Is5060' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q 'plain030T50Is8320' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q 'bothDerivativeSummariesAreTwoRunPrelims' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q 'dashigPrelimIsPrakashMartinReproduction' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q 'dashigDerivativeComparisonRemainsTwoRunPrelim' DASHI/Reasoning/RelationRepresentationRegression.agda

grep -q 'mirrorOwnershipImpliesImplementationAuthorship' DASHI/Reasoning/ImplementationExperimentProvenanceExact.agda
grep -q 'canonicalLeechDASHIgProvenance' DASHI/Reasoning/ImplementationExperimentProvenanceExact.agda
grep -q 'heldOutContextSeparatesOffsetFromAffine' DASHI/Reasoning/RelationRepresentationCandidateDiscriminationExact.agda
grep -q 'localPerturbationSeparatesOffsetFromRotation' DASHI/Reasoning/RelationRepresentationCandidateDiscriminationExact.agda
grep -q 'bestFitFamilyIsSemanticRealization' DASHI/Reasoning/RelationRepresentationCandidateDiscriminationExact.agda
grep -q 'RelationMechanismSocket' DASHI/Reasoning/RelationRepresentationMechanismSocketExact.agda
grep -q 'experimentObservationCommutes' DASHI/Reasoning/RelationRepresentationMechanismSocketExact.agda
grep -q 'explicitDiscrepancyCarrierRequiredForStage7' DASHI/Reasoning/RelationRepresentationMechanismSocketExact.agda
grep -q 'realActivationStateCarrierSupplied' DASHI/Reasoning/RelationRepresentationMechanismSocketExact.agda

grep -q 'grokkingDynamicValidation' DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
grep -q 'spectralDiagnosticIsCausalMechanismByDefault' DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
grep -q 'ExternalStudyReceipt' DASHI/Reasoning/RelationRepresentationExternalReceiptAdmissionExact.agda
grep -q 'ExactSVD2' DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda
grep -q 'oneHumourConsumerSafetyDoesNotEstablishPluralSafety' DASHI/Reasoning/HumourRelationRepresentationCrossPollinationExact.agda
grep -q 'neuralSearchMayReopenFromOffsetToRotation' DASHI/Reasoning/NeuralSpectralRelationCrossPollinationExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/Reasoning/ImplementationExperimentProvenanceExact.agda
  agda -i . -i src DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
  agda -i . -i src DASHI/Reasoning/DASHIgGrokkingStage67SpecimenExact.agda
  agda -i . -i src DASHI/Reasoning/RelationRepresentationStudyValidationObligationsExact.agda
  agda -i . -i src DASHI/Reasoning/RelationRepresentationTOEInferenceHandoffExact.agda
  agda -i . -i src DASHI/Reasoning/RelationRepresentationExternalReceiptAdmissionExact.agda
  agda -i . -i src DASHI/Reasoning/RelationRepresentationCandidateDiscriminationExact.agda
  agda -i . -i src DASHI/Reasoning/RelationRepresentationMechanismSocketExact.agda
  agda -i . -i src DASHI/Reasoning/FiniteRelationLinearAlgebraProducerExact.agda
  agda -i . -i src DASHI/Reasoning/FiniteRelationSVDJacobianProducerExact.agda
  agda -i . -i src DASHI/Reasoning/RelationRepresentationRegression.agda
  agda -i . -i src DASHI/Reasoning/Everything.agda
else
  echo "agda unavailable: structural/fail-closed relation-representation scan completed; no kernel-clean claim"
fi
