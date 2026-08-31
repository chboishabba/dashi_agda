module DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact as S

------------------------------------------------------------------------
-- Exact current RH scheduler regression after the 8889 Lean return.
------------------------------------------------------------------------

offOrdinateIsActive :
  S.ActiveHighOrdinateExperiment S.deriveOffOrdinateEvaluation
offOrdinateIsActive = S.activeOff

gammaRepairIsActive :
  S.ActiveHighOrdinateExperiment S.improveGammaEvaluation
gammaRepairIsActive = S.activeGammaRepair

clusterRepeatCannotBeScheduled :
  S.RHBidiSchedulable S.repeatClusterMarginProof → ⊥
clusterRepeatCannotBeScheduled = S.clusterMarginRepeatNotSchedulable

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
