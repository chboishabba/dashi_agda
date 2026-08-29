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
  DASHI/Programmes/CFDExact.agda
  DASHI/Programmes/BrainExact.agda
  DASHI/Programmes/BrainHemibrainExperimentExact.agda
  DASHI/Programmes/QuantumExact.agda
  DASHI/Programmes/QuantumFalsifiableTargetExact.agda
  DASHI/Programmes/DashifineExact.agda
  DASHI/Programmes/GrokkingExact.agda
  DASHI/Programmes/CoreReferenceExact.agda
  DASHI/Programmes/FRACDASHExact.agda
  DASHI/Programmes/TestHarnessExact.agda
  DASHI/Programmes/RTXExact.agda
  DASHI/Programmes/RTXLightTransportRefinementExact.agda
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

# Programme-registry completeness guard: the nine known satellite repositories
# must each have a literal adapter and every adapter is forced through the
# formal-owner + evidence-receipt cutset in ResearchProgrammeValidation.
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

# Substantive satellite sockets.  These names are intentionally theorem-facing,
# not documentation-only markers.
grep -q '^HemibrainMeasurementClosesPrediction :' DASHI/Programmes/BrainHemibrainExperimentExact.agda
grep -q '^hemibrainReceiptDoesNotRemoveMeasurementObligation :' DASHI/Programmes/BrainHemibrainExperimentExact.agda
grep -q '^falsifiableTargetRefutesCurrentEquivalence :' DASHI/Programmes/QuantumFalsifiableTargetExact.agda
grep -q '^iteratedRefinementPreservesObservation :' DASHI/Programmes/RTXLightTransportRefinementExact.agda
grep -q 'lowerMDLIsPhysicalTruthIsFalse' DASHI/Programmes/RTXLightTransportRefinementExact.agda
grep -q 'discriminatorAloneIsQuantumGravityTheoryIsFalse' DASHI/Programmes/QuantumFalsifiableTargetExact.agda

if ! command -v agda >/dev/null 2>&1; then
  echo "Agda executable not available; static TOE experiment/programme checks passed, kernel typecheck not run." >&2
  exit 2
fi

agda -i . -i /usr/share/agda-stdlib DASHI/Core/TOEExperimentArchitectureValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Programmes/ResearchProgrammeValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Programmes/Everything.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Core/Everything.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/Everything.agda

echo "TOE experiment and cross-repository programme architecture checks passed."
