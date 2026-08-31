#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Reasoning/AristotleExperimentalProofSearchExact.agda
  DASHI/Reasoning/AristotleExperimentalBranchMergeExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientLeanReturn8889Exact.agda
  DASHI/Analysis/RiemannAristotleExperimentalProofSearchExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientFiniteNearRouteAuditExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientDirectFiniteNearAttackExact.agda
  DASHI/Analysis/RiemannAristotlePoleNearPhaseStatisticExact.agda
  DASHI/Analysis/RiemannAristotlePoleNearTargetModulationExact.agda
  DASHI/Analysis/RiemannConstructedComplexCharacterCoreExact.agda
  DASHI/Analysis/RiemannConstructedRealPhaseCoherenceExact.agda
  DASHI/Analysis/RiemannConstructedComplexExpAddReductionExact.agda
  DASHI/Analysis/RiemannAnalyticComplexCharacterExtensionExact.agda
  DASHI/Analysis/RiemannPoleNearReflectionEvenNormalizationExact.agda
  DASHI/Analysis/RiemannAnalyticTestModulationShiftExact.agda
  DASHI/Analysis/RiemannAnalyticModulationExtensionExact.agda
  DASHI/Analysis/RiemannAnalyticModulationBidiAssemblyExact.agda
  DASHI/Analysis/RiemannPoleNearHTAnalyticAdapterExact.agda
  DASHI/Analysis/RiemannAristotlePoleNearTranslationModulationIntertwinerExact.agda
  DASHI/Analysis/RiemannAristotlePoleNearWindowRestrictionResidualExact.agda
  DASHI/Analysis/RiemannAristotlePoleNearTranslationModulationBidiMeetingExact.agda
  DASHI/Analysis/RiemannAristotlePoleNearExplicitFormulaBridgeExact.agda
  DASHI/Analysis/RiemannAristotlePoleNearBidiMeetingExact.agda
  DASHI/Analysis/RiemannAristotleRHBidiSearchSchedulerExact.agda
  DASHI/Analysis/RiemannAristotleRHBidiSearchSchedulerRegression.agda
  DASHI/Analysis/RiemannAristotleRHAnalyticRouteSchedulerExact.agda
  DASHI/Analysis/RiemannAristotleRHAnalyticLeafSchedulerExact.agda
  DASHI/Reasoning/AristotleExperimentalProofSearchValidation.agda
)

for f in "${FILES[@]}"; do
  if grep -nE '(^|[^A-Za-z])(postulate|{-# *TERMINATING|{-# *NON_TERMINATING)' "$f"; then
    echo "trust-scan failure in $f" >&2
    exit 1
  fi
done

if command -v agda >/dev/null 2>&1; then
  agda DASHI/Reasoning/AristotleExperimentalProofSearchValidation.agda
else
  echo "agda executable not present; trust scan only" >&2
fi
