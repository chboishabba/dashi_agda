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
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required TOE experiment source is missing: $file" >&2; exit 1; }
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

if ! command -v agda >/dev/null 2>&1; then
  echo "Agda executable not available; static TOE experiment checks passed, kernel typecheck not run." >&2
  exit 2
fi

agda -i . -i /usr/share/agda-stdlib DASHI/Core/TOEExperimentArchitectureValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Core/Everything.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/Everything.agda

echo "TOE experiment architecture checks passed."
