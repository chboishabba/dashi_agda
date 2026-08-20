module DASHI.Papers.NavierStokes.TheoremInterfaceRound80Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND80 INTERFACE
--
-- The Round79 individual-eigenframe denominator is replaced by an exhaustive
-- spectral architecture:
--
--   separated top-vs-lower cluster
--   OR separated upper-vs-bottom cluster
--   OR both adjacent gaps small, hence the full trace-free strain spectrum
--      is small in the exact gap coordinates.
--
-- Spectral projectors eliminate internal basis gauge but do not remove the
-- cluster-complement separation required by Davis--Kahan.  Directional
-- observables that do not descend to the cluster quotient remain explicit.
--
-- The repo's pre-existing spectralProjectorTurnoverCurrency is now welded to
-- the deterministic coherence-budget residence theorem.  Foias--Rosa--Temam
-- is retained as rigorous statistical-sojourn context, not promoted to the
-- selected-trajectory deterministic residence estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound80Exact as R80

round80SpectralProjectorFixesInternalBasisGauge : Bool
round80SpectralProjectorFixesInternalBasisGauge =
  R80.round80ProjectorsRemoveInternalBasisGauge

round80SpectralProjectorMakesGapAssumptionDisappear : Bool
round80SpectralProjectorMakesGapAssumptionDisappear =
  R80.round80ProjectorsMakeC4GapFree

round80TraceFreeClusterOrSmallSpectrumFork : Bool
round80TraceFreeClusterOrSmallSpectrumFork =
  R80.round80ClusterOrSmallSpectrumForkConstructed

round80ProjectorTurnoverUsesExistingResidenceKernel : Bool
round80ProjectorTurnoverUsesExistingResidenceKernel =
  R80.round80ProjectorTurnoverFeedsExistingResidence

round80StatisticalPositiveSojournIsDeterministicSelectedResidenceBound : Bool
round80StatisticalPositiveSojournIsDeterministicSelectedResidenceBound =
  R80.round80FoiasPositiveSojournClosesSelectedResidence

-- Seven remaining physical/analytic packages.
round80SelectedGlobalLiteralGalerkinTrajectory : Bool
round80SelectedGlobalLiteralGalerkinTrajectory = false

round80SelectedFineStructuredDynamicBalance : Bool
round80SelectedFineStructuredDynamicBalance = false

round80PhysicalPressureProjectorOrSmallStrainSurplusDepletionClosure : Bool
round80PhysicalPressureProjectorOrSmallStrainSurplusDepletionClosure = false

round80PhysicalNormalizedSixThreeGramEstimate : Bool
round80PhysicalNormalizedSixThreeGramEstimate = false

round80PhysicalHHBadCapacityChargeBound : Bool
round80PhysicalHHBadCapacityChargeBound = false

round80PhysicalSoftDataAndBoundaryClosure : Bool
round80PhysicalSoftDataAndBoundaryClosure = false

round80PhysicalAnnularMultiplierKernelBound : Bool
round80PhysicalAnnularMultiplierKernelBound = false

round80CriticalRatioBarrier : Bool
round80CriticalRatioBarrier = false

round80GenericAubinLionsLimitInterfacesAlreadyPresent : Bool
round80GenericAubinLionsLimitInterfacesAlreadyPresent =
  R80.round80GenericAubinLionsLimitInterfacesAlreadyPresent

round80CriticalToSerrinReducerAlreadyPresent : Bool
round80CriticalToSerrinReducerAlreadyPresent =
  R80.round80CriticalToSerrinReducerAlreadyPresent

round80ClayPromotion : Bool
round80ClayPromotion = false

round80SpectralProjectorMakesGapAssumptionDisappearIsFalse :
  round80SpectralProjectorMakesGapAssumptionDisappear ≡ false
round80SpectralProjectorMakesGapAssumptionDisappearIsFalse = refl

round80TraceFreeClusterOrSmallSpectrumForkIsTrue :
  round80TraceFreeClusterOrSmallSpectrumFork ≡ true
round80TraceFreeClusterOrSmallSpectrumForkIsTrue = refl

round80ProjectorTurnoverUsesExistingResidenceKernelIsTrue :
  round80ProjectorTurnoverUsesExistingResidenceKernel ≡ true
round80ProjectorTurnoverUsesExistingResidenceKernelIsTrue = refl

round80StatisticalPositiveSojournIsDeterministicSelectedResidenceBoundIsFalse :
  round80StatisticalPositiveSojournIsDeterministicSelectedResidenceBound ≡ false
round80StatisticalPositiveSojournIsDeterministicSelectedResidenceBoundIsFalse = refl

round80ClayPromotionIsFalse : round80ClayPromotion ≡ false
round80ClayPromotionIsFalse = refl
