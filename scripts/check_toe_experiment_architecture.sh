#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/PredictionEnvelopeExact.agda
  DASHI/Core/CalibratedExperimentInferenceExact.agda
  DASHI/Core/RobustExperimentInferenceFrontierExact.agda
  DASHI/Core/TOEExperimentArchitectureValidation.agda
  DASHI/Physics/Foundations/PhysicalTheoryExperimentDiscriminationExact.agda
  DASHI/Programmes/ResearchProgrammeExact.agda
  DASHI/Programmes/BidirectionalSatelliteCorrectionExact.agda
  DASHI/Programmes/ExecutableReceiptSchemaExact.agda
  DASHI/Programmes/CFDExact.agda
  DASHI/Programmes/CFDChartCorrectionExact.agda
  DASHI/Programmes/BrainExact.agda
  DASHI/Programmes/BrainHemibrainExperimentExact.agda
  DASHI/Programmes/BrainKernelSemanticsCorrectionExact.agda
  DASHI/Programmes/QuantumExact.agda
  DASHI/Programmes/QuantumFalsifiableTargetExact.agda
  DASHI/Programmes/DashifineExact.agda
  DASHI/Programmes/DashifineBenchmarkCorrectionExact.agda
  DASHI/Programmes/GrokkingExact.agda
  DASHI/Programmes/GrokkingValidationCorrectionExact.agda
  DASHI/Programmes/GrokkingHeldOutToleranceExact.agda
  DASHI/Programmes/CoreReferenceExact.agda
  DASHI/Programmes/CoreReferenceCorrectionExact.agda
  DASHI/Programmes/FRACDASHExact.agda
  DASHI/Programmes/FRACDASHCompilerCorrectionExact.agda
  DASHI/Programmes/FRACDASHNumericInterpreterTargetExact.agda
  DASHI/Programmes/TestHarnessExact.agda
  DASHI/Programmes/TestHarnessEvidenceCorrectionExact.agda
  DASHI/Programmes/RTXExact.agda
  DASHI/Programmes/RTXLightTransportRefinementExact.agda
  DASHI/Programmes/BidirectionalSatelliteValidation.agda
  DASHI/Programmes/Everything.agda
  DASHI/Programmes/ResearchProgrammeValidation.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required TOE experiment/programme source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'envelopeCarriesProbabilityWeightsByDefinitionIsFalse' DASHI/Core/PredictionEnvelopeExact.agda
grep -q 'posteriorMassEqualsFrequentistCoverageIsFalse' DASHI/Core/CalibratedExperimentInferenceExact.agda
grep -q 'declaredSensitivityIsAutomaticallyCertifiedIsFalse' DASHI/Core/CalibratedExperimentInferenceExact.agda
grep -q 'calibratedFitDeterminesModelAdequacyIsFalse' DASHI/Core/RobustExperimentInferenceFrontierExact.agda
grep -q 'repairThatFitsTrainingIsScientificallySupportedIsFalse' DASHI/Core/RobustExperimentInferenceFrontierExact.agda
grep -q 'sharedMathematicsIsPhysicalUnificationIsFalse' DASHI/Physics/Foundations/PhysicalTheoryExperimentDiscriminationExact.agda
grep -q 'candidateFitIsEstablishedTheoryRecoveryIsFalse' DASHI/Physics/Foundations/PhysicalTheoryExperimentDiscriminationExact.agda

for witness in \
  cfdOwner brainOwner quantumOwner dashifineOwner grokkingOwner \
  coreOwner fracdashOwner testHarnessOwner rtxOwner \
  cfdReceipt brainReceipt quantumReceipt dashifineReceipt grokkingReceipt \
  coreReceipt fracdashReceipt testHarnessReceipt rtxReceipt; do
  grep -q "^${witness} :" DASHI/Programmes/ResearchProgrammeValidation.agda || {
    echo "missing programme coverage witness: ${witness}" >&2
    exit 1
  }
done

grep -q '^HemibrainMeasurementClosesPrediction :' DASHI/Programmes/BrainHemibrainExperimentExact.agda
grep -q '^falsifiableTargetRefutesCurrentEquivalence :' DASHI/Programmes/QuantumFalsifiableTargetExact.agda
grep -q '^iteratedRefinementPreservesObservation :' DASHI/Programmes/RTXLightTransportRefinementExact.agda

grep -q '^correctedSatelliteYieldsClaimTransport :' DASHI/Programmes/BidirectionalSatelliteCorrectionExact.agda
grep -q '^informationLossBlocksCorrectedBridge :' DASHI/Programmes/BidirectionalSatelliteCorrectionExact.agda
grep -q '^collisionForcesRepresentationRepair :' DASHI/Programmes/CFDChartCorrectionExact.agda
grep -q 'localSignKernelIsAutomaticallyIdempotentIsFalse' DASHI/Programmes/BrainKernelSemanticsCorrectionExact.agda
grep -q 'oneTaskDominanceIsUniversalLearningIsFalse' DASHI/Programmes/DashifineBenchmarkCorrectionExact.agda
grep -q 'twoPointPerfectTimingFitIsUniversalLawIsFalse' DASHI/Programmes/GrokkingValidationCorrectionExact.agda
grep -q '^combinedApproximateFamilyLaw :' DASHI/Programmes/GrokkingHeldOutToleranceExact.agda
grep -q 'postHocToleranceIsIndependentValidationIsFalse' DASHI/Programmes/GrokkingHeldOutToleranceExact.agda
grep -q 'backendFingerprintEqualityIsStateEqualityIsFalse' DASHI/Programmes/CoreReferenceCorrectionExact.agda
grep -q '^finiteTraceCommutes :' DASHI/Programmes/FRACDASHCompilerCorrectionExact.agda
grep -q '^finiteTraceReadoutCorrect :' DASHI/Programmes/FRACDASHCompilerCorrectionExact.agda
grep -q '^blockedPrefixChoosesNext :' DASHI/Programmes/FRACDASHNumericInterpreterTargetExact.agda
grep -q '^receiptYieldsFirstApplicableStep :' DASHI/Programmes/FRACDASHNumericInterpreterTargetExact.agda
grep -q 'remainingGapIsFloatingPointApproximationIsFalse' DASHI/Programmes/FRACDASHNumericInterpreterTargetExact.agda
grep -q 'finiteRunObservationIsGlobalTheoremIsFalse' DASHI/Programmes/ExecutableReceiptSchemaExact.agda
grep -q 'selectedGramIsUniformFrameTheoremIsFalse' DASHI/Programmes/ExecutableReceiptSchemaExact.agda
grep -q '^receiptPlusUniquenessPinsPrediction :' DASHI/Programmes/TestHarnessEvidenceCorrectionExact.agda
grep -q 'lowerMDLIsPhysicalTruthIsFalse' DASHI/Programmes/RTXLightTransportRefinementExact.agda
grep -q 'discriminatorAloneIsQuantumGravityTheoryIsFalse' DASHI/Programmes/QuantumFalsifiableTargetExact.agda

if ! command -v agda >/dev/null 2>&1; then
  echo "Agda executable not available; static TOE experiment/programme/BIDI checks passed, kernel typecheck not run." >&2
  exit 2
fi

agda -i . -i /usr/share/agda-stdlib DASHI/Core/TOEExperimentArchitectureValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Programmes/ResearchProgrammeValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Programmes/BidirectionalSatelliteValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Programmes/Everything.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Core/Everything.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/Everything.agda

echo "TOE experiment, cross-repository programme, and BIDI correction checks passed."
