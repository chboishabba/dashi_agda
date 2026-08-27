module DASHI.Governance.Fanning2022ProjectionBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Core.ThresholdResidualTrajectoryGeometryExact as Threshold
import DASHI.Governance.Fanning2022TemporalIndicatorExact as Fanning
import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- FANNING 2022: COUNT / EXTENT / DOUGHNUT / TRAJECTORY PROJECTION BOUNDARY
--
-- The paper exposes several distinct published views:
--   Fig. 2 : threshold counts over time;
--   Fig. 3 : extent of social shortfall vs ecological overshoot;
--   Fig. 4 : historical and BAU trajectories;
--   Fig. 5 : indicator-level country doughnuts.
--
-- These views are not silently identified.  In particular, threshold status
-- loses magnitude, and aggregate residual magnitude loses coordinate identity.
-- The finite witnesses below are generic projection counterexamples calibrated
-- to this representational distinction; they are not claimed to reproduce the
-- paper's exact normalization constants.
------------------------------------------------------------------------

data PublishedView : Set where
  thresholdCountView extentView temporalTrendView indicatorDoughnutView : PublishedView

data DomainAxis : Set where
  socialShortfallAxis ecologicalOvershootAxis : DomainAxis

figure2View figure3View figure4View figure5View : PublishedView
figure2View = thresholdCountView
figure3View = extentView
figure4View = temporalTrendView
figure5View = indicatorDoughnutView

------------------------------------------------------------------------
-- Threshold count/status does not recover magnitude.
------------------------------------------------------------------------

sameThresholdFailureStatus :
  Threshold.withinThreshold Threshold.nearHigherFailure ≡
  Threshold.withinThreshold Threshold.farHigherFailure
sameThresholdFailureStatus = Threshold.sameHigherFailureStatus

sameThresholdStatusDoesNotRecoverDistance :
  Threshold.thresholdResidual Threshold.nearHigherFailure ≡
  Threshold.thresholdResidual Threshold.farHigherFailure → ⊥
sameThresholdStatusDoesNotRecoverDistance =
  Threshold.sameStatusDoesNotRecoverResidual

------------------------------------------------------------------------
-- Aggregate extent does not recover the indicator-residual vector.
------------------------------------------------------------------------

sameExtentDifferentIndicatorAllocation :
  Threshold.aggregateResidual Threshold.residualA ≡
  Threshold.aggregateResidual Threshold.residualB
sameExtentDifferentIndicatorAllocation = Threshold.sameAggregateResidual

sameExtentDoesNotRecoverFirstIndicatorResidual :
  Threshold.firstResidual Threshold.residualA ≡
  Threshold.firstResidual Threshold.residualB → ⊥
sameExtentDoesNotRecoverFirstIndicatorResidual =
  Threshold.sameAggregateDoesNotRecoverFirstCoordinate

------------------------------------------------------------------------
-- Social improvement and ecological improvement are independent coordinates.
------------------------------------------------------------------------

sameJointMagnitudeWithSocialEcologicalTradeoff :
  Threshold.jointResidual Threshold.trajectoryStart ≡
  Threshold.jointResidual Threshold.socialBetterEcoWorse
sameJointMagnitudeWithSocialEcologicalTradeoff =
  Threshold.sameJointResidualDespiteTradeoff

oppositeTradeoffsCanShareAggregateMagnitude :
  Threshold.jointResidual Threshold.socialBetterEcoWorse ≡
  Threshold.jointResidual Threshold.ecoBetterSocialWorse
oppositeTradeoffsCanShareAggregateMagnitude =
  Threshold.oppositeTradeoffSameAggregate

------------------------------------------------------------------------
-- Source/evidence-role boundary.
------------------------------------------------------------------------

source : Sources.SourceReference
source = Sources.fanning2022

record FanningProjectionBoundary : Set where
  constructor fanningProjectionBoundary
  field
    countViewEqualsExtentView : Bool
    countViewEqualsExtentViewIsFalse : countViewEqualsExtentView ≡ false
    extentViewRecoversIndicatorVector : Bool
    extentViewRecoversIndicatorVectorIsFalse :
      extentViewRecoversIndicatorVector ≡ false
    socialImprovementForcesEcologicalImprovement : Bool
    socialImprovementForcesEcologicalImprovementIsFalse :
      socialImprovementForcesEcologicalImprovement ≡ false
    historicalTrendEqualsProjectedBAUPath : Bool
    historicalTrendEqualsProjectedBAUPathIsFalse :
      historicalTrendEqualsProjectedBAUPath ≡ false
    BAUProjectionIsObserved2050Outcome : Bool
    BAUProjectionIsObserved2050OutcomeIsFalse :
      BAUProjectionIsObserved2050Outcome ≡ false
    nationalPanelUsesSameSevenBiophysicalCoordinatesAs2018 : Bool
    nationalPanelUsesSameSevenBiophysicalCoordinatesAs2018IsFalse :
      nationalPanelUsesSameSevenBiophysicalCoordinatesAs2018 ≡ false

canonicalFanningProjectionBoundary : FanningProjectionBoundary
canonicalFanningProjectionBoundary =
  fanningProjectionBoundary false refl false refl false refl false refl false refl false refl
