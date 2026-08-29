#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/ExperimentalCoordinateDesignExact.agda
  DASHI/Core/ActionabilityCostedExperimentChoiceExact.agda
  DASHI/Core/CommonExperimentRealisationExact.agda
  DASHI/Core/DiscriminatorSynthesisExact.agda
  DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
  DASHI/Core/SequentialRobustActionabilityPlannerExact.agda
  DASHI/Core/SequentialRelationalExperimentPlannerExact.agda
  DASHI/Core/SequentialExperimentPlanningValidation.agda
  DASHI/Physics/Foundations/GRQFTDiscriminatorSynthesisExact.agda
  DASHI/Physics/Foundations/GRQFTSequentialExperimentPlannerExact.agda
  DASHI/Environment/LESDiscriminatorSynthesisExact.agda
  DASHI/Environment/LESSequentialExperimentPlannerExact.agda
  DASHI/Environment/LESAdaptiveConsumerLoopCrossPollinationExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required sequential experiment source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^data SequentialConsumerPlan' DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
grep -q '^OutcomePossible :' DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
grep -q '^oneShotConsumerClosingPlan :' DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
grep -q '^data SequentialActionabilityPlan' DASHI/Core/SequentialRobustActionabilityPlannerExact.agda
grep -q '^robustActionSurvivesMeasuredRefinement :' DASHI/Core/SequentialRobustActionabilityPlannerExact.agda
grep -q '^data SequentialRelationalPlan' DASHI/Core/SequentialRelationalExperimentPlannerExact.agda
grep -q 'everyHypothesisMustPredictOneDeterministicOutcomeIsFalse' DASHI/Core/SequentialRelationalExperimentPlannerExact.agda
grep -q '^record SequentialPhysicalExperimentProgramme' DASHI/Physics/Foundations/GRQFTSequentialExperimentPlannerExact.agda
grep -q '^record LESSequentialConsumerExperiment' DASHI/Environment/LESSequentialExperimentPlannerExact.agda
grep -q '^record LESSequentialActionabilityExperiment' DASHI/Environment/LESSequentialExperimentPlannerExact.agda
grep -q 'sequentialPlanningRequiresFixedMeasurementOrderIsFalse' DASHI/Environment/LESAdaptiveConsumerLoopCrossPollinationExact.agda

scripts/run_agda29_parallel_check.sh DASHI/Core/SequentialExperimentPlanningValidation.agda
