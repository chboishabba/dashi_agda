#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Analysis/RiemannAristotleWindowSchurCrossProverSyncExact.agda
  DASHI/Analysis/RiemannAristotleWindowSchurCrossProverRegression.agda
  DASHI/Analysis/RiemannAristotleSharedWindowCertificateExact.agda
  DASHI/Analysis/RiemannAristotleTwoZeroThreeTaperReturnExact.agda
  DASHI/Analysis/RiemannAristotleTwoZeroThreeTaperReturnRegression.agda
  DASHI/Analysis/ExactSelectedEliminationFarTailCompilerExact.agda
  DASHI/Analysis/RiemannAristotleABCDECompilerExact.agda
  DASHI/Analysis/RiemannAristotleABCDECompilerRegression.agda
  DASHI/Analysis/RiemannAristotleTwoZeroUniversalRHBoundary.agda
  DASHI/Analysis/RiemannAristotleTwoZeroUniversalRHBoundaryRegression.agda
  DASHI/Analysis/RiemannAristotleProjectedCarrierLeanReturnExact.agda
  DASHI/Analysis/RiemannAristotleUniversalEvenConeBidiExact.agda
  DASHI/Analysis/ReflectionPairSignedKernelCompilerExact.agda
  DASHI/Analysis/RiemannAristotleReflectionPairKernelReturnExact.agda
  DASHI/Analysis/RiemannAristotleReflectionSymmetrizationReturnExact.agda
  DASHI/Analysis/RiemannAristotleDeterministicProjectiveSchurReturnExact.agda
  DASHI/Analysis/RiemannAristotleProjectedZeroTailSummabilityReturnExact.agda
  DASHI/Analysis/RiemannAristotleExplicitCutoffCarrierLeanReturnExact.agda
  DASHI/Analysis/RiemannAristotleWholeCarrierCancellationCompilerExact.agda
  DASHI/Analysis/RiemannAristotleNearFarShellBudgetCompilerExact.agda
  DASHI/Analysis/RiemannAristotleNearFarShellProducerSocketsExact.agda
  DASHI/Analysis/RiemannAristotleNearFarShellCompositionExact.agda
  DASHI/Analysis/RiemannAristotleFarTailCutoffSelectorExact.agda
  DASHI/Analysis/RiemannAristotleNearFarAllowanceCompositionExact.agda
  DASHI/Analysis/RiemannAristotleFiniteNearCoreSchurCompilerExact.agda
  DASHI/Analysis/RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact.agda
  DASHI/Analysis/RiemannAristotleZetaLocalCountLeanReturnExact.agda
  DASHI/Analysis/RiemannG2GapSplitClusteringLeanReturn8894Exact.agda
  DASHI/Analysis/RiemannG2AdaptiveJLambdaConstantWindowExact.agda
  DASHI/Analysis/RiemannG2QuarterPeriodAnalyticRouteReconciliationExact.agda
  DASHI/Analysis/RiemannG2HighestAlphaAfter8894Exact.agda
  DASHI/Analysis/RiemannAristotleRHBidiSearchSchedulerExact.agda
  DASHI/Analysis/RiemannAristotleRHAnalyticLeafSchedulerExact.agda
  DASHI/Analysis/RiemannAristotleNearCoreDensityReturnRegression.agda
  DASHI/Analysis/RiemannAristotleCurrentFrontierExact.agda
  DASHI/Analysis/RiemannAristotleCurrentFrontierRegression.agda
  DASHI/Analysis/RiemannAristotleSharedCertificateREADME.agda
)

for f in "${FILES[@]}"; do
  if grep -nE '(^|[^A-Za-z])(postulate|{-# *TERMINATING|{-# *NON_TERMINATING)' "$f"; then
    echo "trust-scan failure in $f" >&2
    exit 1
  fi
done

if command -v agda >/dev/null 2>&1; then
  agda DASHI/Analysis/RiemannAristotleWindowSchurCrossProverRegression.agda
  agda DASHI/Analysis/RiemannAristotleTwoZeroThreeTaperReturnRegression.agda
  agda DASHI/Analysis/ExactSelectedEliminationFarTailCompilerExact.agda
  agda DASHI/Analysis/RiemannAristotleABCDECompilerRegression.agda
  agda DASHI/Analysis/RiemannAristotleTwoZeroUniversalRHBoundaryRegression.agda
  agda DASHI/Analysis/RiemannAristotleProjectedCarrierLeanReturnExact.agda
  agda DASHI/Analysis/RiemannAristotleUniversalEvenConeBidiExact.agda
  agda DASHI/Analysis/ReflectionPairSignedKernelCompilerExact.agda
  agda DASHI/Analysis/RiemannAristotleReflectionPairKernelReturnExact.agda
  agda DASHI/Analysis/RiemannAristotleReflectionSymmetrizationReturnExact.agda
  agda DASHI/Analysis/RiemannAristotleDeterministicProjectiveSchurReturnExact.agda
  agda DASHI/Analysis/RiemannAristotleProjectedZeroTailSummabilityReturnExact.agda
  agda DASHI/Analysis/RiemannAristotleExplicitCutoffCarrierLeanReturnExact.agda
  agda DASHI/Analysis/RiemannAristotleWholeCarrierCancellationCompilerExact.agda
  agda DASHI/Analysis/RiemannAristotleNearFarShellBudgetCompilerExact.agda
  agda DASHI/Analysis/RiemannAristotleNearFarShellProducerSocketsExact.agda
  agda DASHI/Analysis/RiemannAristotleNearFarShellCompositionExact.agda
  agda DASHI/Analysis/RiemannAristotleFarTailCutoffSelectorExact.agda
  agda DASHI/Analysis/RiemannAristotleNearFarAllowanceCompositionExact.agda
  agda DASHI/Analysis/RiemannAristotleFiniteNearCoreSchurCompilerExact.agda
  agda DASHI/Analysis/RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact.agda
  agda DASHI/Analysis/RiemannAristotleZetaLocalCountLeanReturnExact.agda
  agda DASHI/Analysis/RiemannG2GapSplitClusteringLeanReturn8894Exact.agda
  agda DASHI/Analysis/RiemannG2AdaptiveJLambdaConstantWindowExact.agda
  agda DASHI/Analysis/RiemannG2QuarterPeriodAnalyticRouteReconciliationExact.agda
  agda DASHI/Analysis/RiemannG2HighestAlphaAfter8894Exact.agda
  agda DASHI/Analysis/RiemannAristotleRHBidiSearchSchedulerExact.agda
  agda DASHI/Analysis/RiemannAristotleRHAnalyticLeafSchedulerExact.agda
  agda DASHI/Analysis/RiemannAristotleNearCoreDensityReturnRegression.agda
  agda DASHI/Analysis/RiemannAristotleCurrentFrontierRegression.agda
  agda DASHI/Analysis/RiemannAristotleSharedCertificateREADME.agda
else
  echo "agda executable not present; trust scan only" >&2
fi
