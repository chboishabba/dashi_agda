#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_dynamic_mass_residual_round11.sh"
if [[ -x "$BASE_CHECKER" ]]; then
  "$BASE_CHECKER"
fi

FILES=(
  DASHI/Core/FutureObservationLanguageQuotientExact.agda
  DASHI/Core/DynamicProjectionCompositionExact.agda
  DASHI/Core/PathDependentAccessibilityExact.agda
  DASHI/Core/FiniteOptimalResidualSelectorExact.agda
  DASHI/Cognition/PNF/ConstraintNetworkObstructionExact.agda
  DASHI/Cognition/PNF/PhasedRelationalEvidencePropagationExact.agda
  DASHI/Cognition/PNF/SpokenTelescopeConsumerProjectionExact.agda
  DASHI/Cognition/PNF/ExactVsRelevantResidualExact.agda
  DASHI/Cognition/PNF/WikidataTypePressureMiniWorldExact.agda
  DASHI/Foundations/DepthWheelStroboscopicContractionExact.agda
  DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'futureEquivalentRefl' DASHI/Core/FutureObservationLanguageQuotientExact.agda
grep -q 'futureEquivalentSym' DASHI/Core/FutureObservationLanguageQuotientExact.agda
grep -q 'futureEquivalentTrans' DASHI/Core/FutureObservationLanguageQuotientExact.agda
grep -q 'safeProjectionKernelFactorsThroughFutureEquivalence' DASHI/Core/FutureObservationLanguageQuotientExact.agda
grep -q 'sectionedSafeProjectionFactors' DASHI/Core/FutureObservationLanguageQuotientExact.agda

grep -q 'composeDynamicProjection' DASHI/Core/DynamicProjectionCompositionExact.agda
grep -q 'compositeTraceCommutes' DASHI/Core/DynamicProjectionCompositionExact.agda
grep -q 'compositeEqualNowGivesEqualAfterTrace' DASHI/Core/DynamicProjectionCompositionExact.agda

grep -q 'finiteHistoryChangesFutureCone' DASHI/Core/PathDependentAccessibilityExact.agda
grep -q 'hiddenPhaseFiniteOptimalResidual' DASHI/Core/FiniteOptimalResidualSelectorExact.agda
grep -q 'triangleUnsatisfiable' DASHI/Cognition/PNF/ConstraintNetworkObstructionExact.agda
grep -q 'triangleFrustrationStrictlyPositive' DASHI/Cognition/PNF/ConstraintNetworkObstructionExact.agda
grep -q 'costOneWitness' DASHI/Cognition/PNF/ConstraintNetworkObstructionExact.agda

grep -q 'expandedSemanticPhaseIsPositive' DASHI/Cognition/PNF/PhasedRelationalEvidencePropagationExact.agda
grep -q 'processPhaseUnchangedAcrossEvidenceExpansion' DASHI/Cognition/PNF/PhasedRelationalEvidencePropagationExact.agda
grep -q 'futureObservationSeparatesParses' DASHI/Cognition/PNF/SpokenTelescopeConsumerProjectionExact.agda
grep -q 'whoSeenOnlyCannotReopenBothExactly' DASHI/Cognition/PNF/ExactVsRelevantResidualExact.agda
grep -q 'seriesEditionMismatchUnderspecifies' DASHI/Cognition/PNF/WikidataTypePressureMiniWorldExact.agda

grep -q 'oneWheelStrictlyContracts' DASHI/Foundations/DepthWheelStroboscopicContractionExact.agda
grep -q 'stroboscopicStepContracts' DASHI/Foundations/DepthWheelStroboscopicContractionExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
else
  echo "agda unavailable: structural/fail-closed round-13 scan completed; no kernel-clean claim"
fi
