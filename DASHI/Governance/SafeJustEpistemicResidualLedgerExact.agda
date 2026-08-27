module DASHI.Governance.SafeJustEpistemicResidualLedgerExact where

open import DASHI.Core.Prelude
import DASHI.Governance.Fanning2022TemporalIndicatorExact as Temporal

------------------------------------------------------------------------
-- PHENOMENON RESIDUAL != EPISTEMIC / PROOF RESIDUAL
--
-- Threshold/overshoot residuals describe the represented world surface.
-- The residuals below instead describe limitations of the evidence/claim
-- pipeline.  The two roles are intentionally different types.
------------------------------------------------------------------------

data PhenomenonResidual : Set where
  socialShortfallResidual ecologicalOvershootResidual : PhenomenonResidual

data EpistemicResidual : Set where
  missingNationalBlueWaterSeries
  heterogeneousTemporalCoverage
  projectionIsNotObservation
  predictionIntervalUncertainty
  aggregateErasesIndicatorCoordinates
  : EpistemicResidual

data EvidenceStage : Set where
  fanningHistoricalStage
  fanningProjectionStage
  kallisSynthesisStage
  : EvidenceStage

data Carries : EvidenceStage → EpistemicResidual → Set where
  historicalBlueWater : Carries fanningHistoricalStage missingNationalBlueWaterSeries
  historicalCoverage : Carries fanningHistoricalStage heterogeneousTemporalCoverage
  projectionBlueWater : Carries fanningProjectionStage missingNationalBlueWaterSeries
  projectionCoverage : Carries fanningProjectionStage heterogeneousTemporalCoverage
  projectionNotObserved : Carries fanningProjectionStage projectionIsNotObservation
  projectionUncertainty : Carries fanningProjectionStage predictionIntervalUncertainty
  projectionAggregateLoss : Carries fanningProjectionStage aggregateErasesIndicatorCoordinates
  synthesisBlueWater : Carries kallisSynthesisStage missingNationalBlueWaterSeries
  synthesisCoverage : Carries kallisSynthesisStage heterogeneousTemporalCoverage
  synthesisProjectionNotObserved : Carries kallisSynthesisStage projectionIsNotObservation
  synthesisProjectionUncertainty : Carries kallisSynthesisStage predictionIntervalUncertainty
  synthesisAggregateLoss : Carries kallisSynthesisStage aggregateErasesIndicatorCoordinates

data Discharges : EvidenceStage → EpistemicResidual → Set where

historicalResidualSurvivesProjection :
  (r : EpistemicResidual) →
  Carries fanningHistoricalStage r →
  Carries fanningProjectionStage r
historicalResidualSurvivesProjection missingNationalBlueWaterSeries historicalBlueWater = projectionBlueWater
historicalResidualSurvivesProjection heterogeneousTemporalCoverage historicalCoverage = projectionCoverage

projectionResidualSurvivesSynthesis :
  (r : EpistemicResidual) →
  Carries fanningProjectionStage r →
  Carries kallisSynthesisStage r
projectionResidualSurvivesSynthesis missingNationalBlueWaterSeries projectionBlueWater = synthesisBlueWater
projectionResidualSurvivesSynthesis heterogeneousTemporalCoverage projectionCoverage = synthesisCoverage
projectionResidualSurvivesSynthesis projectionIsNotObservation projectionNotObserved = synthesisProjectionNotObserved
projectionResidualSurvivesSynthesis predictionIntervalUncertainty projectionUncertainty = synthesisProjectionUncertainty
projectionResidualSurvivesSynthesis aggregateErasesIndicatorCoordinates projectionAggregateLoss = synthesisAggregateLoss

blueWaterResidualStillOpenAtSynthesis :
  Carries kallisSynthesisStage missingNationalBlueWaterSeries
blueWaterResidualStillOpenAtSynthesis =
  projectionResidualSurvivesSynthesis
    missingNationalBlueWaterSeries
    (historicalResidualSurvivesProjection
      missingNationalBlueWaterSeries historicalBlueWater)

projectionStatusStillOpenAtSynthesis :
  Carries kallisSynthesisStage projectionIsNotObservation
projectionStatusStillOpenAtSynthesis =
  projectionResidualSurvivesSynthesis projectionIsNotObservation projectionNotObserved

noSilentBlueWaterDischarge :
  Discharges kallisSynthesisStage missingNationalBlueWaterSeries → ⊥
noSilentBlueWaterDischarge ()

noSilentProjectionDischarge :
  Discharges kallisSynthesisStage projectionIsNotObservation → ⊥
noSilentProjectionDischarge ()

------------------------------------------------------------------------
-- Source-visible grounding: these proof roles mirror the already encoded
-- Fanning boundaries, rather than inventing a seventh national time series or
-- treating projections as observations.
------------------------------------------------------------------------

blueWaterUnavailable :
  Temporal.blueWaterHasSuitableNational1992To2015TimeSeries
    Temporal.canonicalFanningTemporalIndicatorBoundary ≡ false
blueWaterUnavailable =
  Temporal.blueWaterHasSuitableNational1992To2015TimeSeriesIsFalse
    Temporal.canonicalFanningTemporalIndicatorBoundary

historicalNotProjection :
  Temporal.historicalObservationIsBAUProjection
    Temporal.canonicalFanningTemporalIndicatorBoundary ≡ false
historicalNotProjection =
  Temporal.historicalObservationIsBAUProjectionIsFalse
    Temporal.canonicalFanningTemporalIndicatorBoundary

record EpistemicResidualBoundary : Set where
  constructor epistemicResidualBoundary
  field
    phenomenonResidualEqualsEvidenceResidual : Bool
    phenomenonResidualEqualsEvidenceResidualIsFalse :
      phenomenonResidualEqualsEvidenceResidual ≡ false
    laterReviewSilentlyDischargesEarlierEvidenceGap : Bool
    laterReviewSilentlyDischargesEarlierEvidenceGapIsFalse :
      laterReviewSilentlyDischargesEarlierEvidenceGap ≡ false
    projectionBecomesObservationWhenSynthesized : Bool
    projectionBecomesObservationWhenSynthesizedIsFalse :
      projectionBecomesObservationWhenSynthesized ≡ false
    aggregateResidualRecoversIndicatorVector : Bool
    aggregateResidualRecoversIndicatorVectorIsFalse :
      aggregateResidualRecoversIndicatorVector ≡ false

canonicalEpistemicResidualBoundary : EpistemicResidualBoundary
canonicalEpistemicResidualBoundary =
  epistemicResidualBoundary false refl false refl false refl false refl
