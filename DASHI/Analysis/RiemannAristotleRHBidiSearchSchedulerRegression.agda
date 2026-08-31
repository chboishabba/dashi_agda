module DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact as S

------------------------------------------------------------------------
-- Exact current RH scheduler regression after recursive H_off refinement.
------------------------------------------------------------------------

cutoffCarrierTransportIsActive :
  S.ActiveHighOrdinateExperiment S.transportCutoffCarrierToPoleQuotient
cutoffCarrierTransportIsActive = S.activeCarrierTransport

finiteNearEvaluationIsActive :
  S.ActiveHighOrdinateExperiment S.evaluateFiniteNearSignedSum
finiteNearEvaluationIsActive = S.activeFiniteNear

gammaRepairIsActive :
  S.ActiveHighOrdinateExperiment S.improveGammaEvaluation
gammaRepairIsActive = S.activeGammaRepair

clusterRepeatCannotBeScheduled :
  S.RHBidiSchedulable S.repeatClusterMarginProof → ⊥
clusterRepeatCannotBeScheduled = S.clusterMarginRepeatNotSchedulable

farShellRepeatCannotBeScheduled :
  S.RHBidiSchedulable S.reproveInfiniteFarShell → ⊥
farShellRepeatCannotBeScheduled = S.farShellRepeatNotSchedulable

balanceCircularityCannotBeScheduled :
  S.RHBidiSchedulable S.sharpenBalanceBudgetRoute → ⊥
balanceCircularityCannotBeScheduled = S.balanceRouteNotSchedulable

nameOnlyHardyDonorCannotBeScheduled :
  S.RHBidiSchedulable S.auditNamedExternalDonor → ⊥
nameOnlyHardyDonorCannotBeScheduled = S.nameOnlyDonorNotSchedulable

highestAlphaSelectionCannotEscapeActiveRHQueue :
  (surface : S.RHBidiCostSurface) →
  (selection : S.HighestAlphaRHExperiment surface) →
  S.ActiveHighOrdinateExperiment (S.selected selection)
highestAlphaSelectionCannotEscapeActiveRHQueue =
  S.highestAlphaAlwaysTargetsActiveRHLeaf
