#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/TwoChannelAllowanceCompositionExact.agda
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
  DASHI/Analysis/RiemannAristotleG2CurrentCutExact.agda
  DASHI/Analysis/RiemannAristotleG2CurrentCutRegression.agda
  DASHI/Analysis/RiemannG2GapSplitClusteringLeanReturn8894Exact.agda
  DASHI/Analysis/RiemannG2AlpogeFurmanClusteringNonDescentExact.agda
  DASHI/Analysis/RiemannG2TransverseVsOrdinateMomentNonDescentExact.agda
  DASHI/Analysis/RiemannG2LowGapClusteringMomentReductionExact.agda
  DASHI/Analysis/RiemannG2TargetCenteredScalarCancellationAssemblyExact.agda
  DASHI/Analysis/RiemannAristotlePoleQuotientDirectFiniteNearAttackExact.agda
  DASHI/Analysis/RiemannG2SelectedTargetLocalMomentSameObjectExact.agda
  DASHI/Analysis/RiemannG2SelectedDirectFiniteMomentBidiExact.agda
  DASHI/Analysis/RiemannAristotlePoleNearPhaseStatisticExact.agda
  DASHI/Analysis/RiemannG2SelectedPoleNearFiniteEvaluationSameObjectExact.agda
  DASHI/Analysis/RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact.agda
  DASHI/Analysis/RiemannG2MinimalNearBudgetFinalOffSlackCompilerExact.agda
  DASHI/Analysis/RiemannG2AdaptiveJLambdaConstantWindowExact.agda
  DASHI/Analysis/RiemannG2QuarterPeriodAnalyticRouteReconciliationExact.agda
  DASHI/Analysis/RiemannG2HighestAlphaAfter369Exact.agda
  DASHI/Analysis/RiemannG2HighestAlphaAfter8894Exact.agda
  DASHI/Analysis/RiemannG2PoleQuotientChannelAllowanceExact.agda
  DASHI/Analysis/RiemannG2PoleQuotientOffAllowanceDirectCompilerExact.agda
  DASHI/Analysis/RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact.agda
  DASHI/Analysis/RiemannG2PoleQuotientOffCoreAllowanceBridgeExact.agda
  DASHI/Analysis/RiemannG2FinalOffAllowanceFactorizationRegression.agda
  DASHI/Analysis/RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact.agda
  DASHI/Analysis/RiemannG2PoleQuotientOffChosenCutoffCompilerExact.agda
  DASHI/Analysis/RiemannG2WindowBudgetToTransportedNearUpperExact.agda
  DASHI/Analysis/RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact.agda
  DASHI/Analysis/RiemannG2SelectedNearBudgetFinalOffSlackCompilerExact.agda
  DASHI/Analysis/RiemannG2SelectedNearBudgetFinalOffSlackRegression.agda
  DASHI/Analysis/RiemannG2SelectedDirectCutoffFinalOffSameObjectExact.agda
  DASHI/Analysis/RiemannG2TargetModulationFinalOffCutoffCompilerExact.agda
  DASHI/Analysis/RiemannG2FinalPoleNearRouteReconciliationExact.agda
  DASHI/Analysis/RiemannG2FinalPoleNearRouteRegression.agda
  DASHI/Analysis/RiemannG2GammaProducerSourceAcquisitionExact.agda
  DASHI/Analysis/RiemannG2GammaCandidateSourceLineageRecoveryExact.agda
  DASHI/Analysis/RiemannG2GammaLineageHighestAlphaReconciliationExact.agda
  DASHI/Analysis/RiemannG2PoleQuotientGammaAllowanceDirectCompilerExact.agda
  DASHI/Analysis/RiemannG2FinalGammaRouteSchedulerRegression.agda
  DASHI/Analysis/RiemannG2FreshSameTaperGammaEnvelopeCompilerExact.agda
  DASHI/Analysis/RiemannG2FreshSameTaperGammaEnvelopeRegression.agda
  DASHI/Analysis/RiemannG2PoleQuotientFinalCutReconciliationExact.agda
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
  agda DASHI/Core/TwoChannelAllowanceCompositionExact.agda
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
  agda DASHI/Analysis/RiemannAristotleG2CurrentCutRegression.agda
  agda DASHI/Analysis/RiemannG2GapSplitClusteringLeanReturn8894Exact.agda
  agda DASHI/Analysis/RiemannG2AlpogeFurmanClusteringNonDescentExact.agda
  agda DASHI/Analysis/RiemannG2TransverseVsOrdinateMomentNonDescentExact.agda
  agda DASHI/Analysis/RiemannG2LowGapClusteringMomentReductionExact.agda
  agda DASHI/Analysis/RiemannG2TargetCenteredScalarCancellationAssemblyExact.agda
  agda DASHI/Analysis/RiemannAristotlePoleQuotientDirectFiniteNearAttackExact.agda
  agda DASHI/Analysis/RiemannG2SelectedTargetLocalMomentSameObjectExact.agda
  agda DASHI/Analysis/RiemannG2SelectedDirectFiniteMomentBidiExact.agda
  agda DASHI/Analysis/RiemannAristotlePoleNearPhaseStatisticExact.agda
  agda DASHI/Analysis/RiemannG2SelectedPoleNearFiniteEvaluationSameObjectExact.agda
  agda DASHI/Analysis/RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact.agda
  agda DASHI/Analysis/RiemannG2MinimalNearBudgetFinalOffSlackCompilerExact.agda
  agda DASHI/Analysis/RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact.agda
  agda DASHI/Analysis/RiemannG2PoleQuotientOffCoreAllowanceBridgeExact.agda
  agda DASHI/Analysis/RiemannG2FinalOffAllowanceFactorizationRegression.agda
  agda DASHI/Analysis/RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact.agda
  agda DASHI/Analysis/RiemannG2PoleQuotientOffChosenCutoffCompilerExact.agda
  agda DASHI/Analysis/RiemannG2WindowBudgetToTransportedNearUpperExact.agda
  agda DASHI/Analysis/RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact.agda
  agda DASHI/Analysis/RiemannG2SelectedNearBudgetFinalOffSlackRegression.agda
  agda DASHI/Analysis/RiemannG2FinalPoleNearRouteRegression.agda
  agda DASHI/Analysis/RiemannG2FreshSameTaperGammaEnvelopeRegression.agda
  agda DASHI/Analysis/RiemannG2PoleQuotientFinalCutReconciliationExact.agda
  agda DASHI/Analysis/RiemannAristotleRHBidiSearchSchedulerExact.agda
  agda DASHI/Analysis/RiemannAristotleRHAnalyticLeafSchedulerExact.agda
  agda DASHI/Analysis/RiemannAristotleNearCoreDensityReturnRegression.agda
  agda DASHI/Analysis/RiemannAristotleCurrentFrontierRegression.agda
  agda DASHI/Analysis/RiemannAristotleSharedCertificateREADME.agda
else
  echo "agda executable not present; trust scan only" >&2
fi
