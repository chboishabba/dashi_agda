module DASHI.Governance.Fanning2022MethodsRegression where

------------------------------------------------------------------------
-- Focused elaboration root for the source-exact Fanning 2022 method chain:
--
-- national indicator/time authority
--   -> social-indicator revision authority
--   -> normalization authority
--   -> clipped shortfall/overshoot components
--   -> within-domain averaging boundary
--   -> count/extent/trajectory/doughnut projections
--   -> BAU model-selection authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Governance.Fanning2022TemporalIndicatorExact as Temporal
import DASHI.Governance.Fanning2022SocialIndicatorRevisionExact as SocialRevision
import DASHI.Governance.Fanning2022NormalizationExact as Normalization
import DASHI.Governance.Fanning2022ProjectionBoundaryExact as Projection
import DASHI.Governance.Fanning2022ForecastAuthorityExact as Forecast

nationalBioCountReceipt : Temporal.fanningNationalBiophysicalCount ≡ 6
nationalBioCountReceipt = refl

socialVocabularyCountReceipt : Temporal.fanningSocialVocabularyCount ≡ 11
socialVocabularyCountReceipt = refl

longevityMeasurementRevisionReceipt :
  SocialRevision.healthyLifeExpectancy ≡ SocialRevision.overallLifeExpectancy → ⊥
longevityMeasurementRevisionReceipt =
  SocialRevision.earlierAndLongitudinalLongevityMeasuresDiffer

povertyThresholdRevisionReceipt :
  SocialRevision.extremePoverty190 ≡ SocialRevision.broaderPoverty550 → ⊥
povertyThresholdRevisionReceipt =
  SocialRevision.earlierAndLongitudinalPovertyLinesDiffer

normalizationAuthoritySeparation :
  Normalization.biophysicalNormalizationAuthority ≡
  Normalization.socialNormalizationAuthority → ⊥
normalizationAuthoritySeparation = Normalization.normalizationAuthoritiesDiffer

socialShortfallClippingReceipt :
  Normalization.socialShortfallComponent 70 ≡ 30
socialShortfallClippingReceipt = refl

ecologicalOvershootClippingReceipt :
  Normalization.ecologicalOvershootComponent 130 ≡ 30
ecologicalOvershootClippingReceipt = refl

withinDomainCompensationCollision :
  Normalization.withinDomainA ≡ Normalization.withinDomainB
withinDomainCompensationCollision = Normalization.sameWithinDomainAverageCode

crossDomainScalarCollision :
  Normalization.combinedNumerator Normalization.socialHeavy ≡
  Normalization.combinedNumerator Normalization.ecoHeavy
crossDomainScalarCollision = Normalization.sameCombinedNumerator

countDoesNotBecomeExtent :
  Projection.countViewEqualsExtentView
    Projection.canonicalFanningProjectionBoundary ≡ false
countDoesNotBecomeExtent = refl

forecastIndicatorCountReceipt : Forecast.indicatorTimeSeriesPerCountry ≡ 17
forecastIndicatorCountReceipt = refl

forecastCountryCountReceipt : Forecast.forecastCountryCount ≡ 148
forecastCountryCountReceipt = refl

aiccDoesNotBecomeCrossFamilyAuthority :
  Forecast.aiccIsValidCrossFamilyETSARIMAComparison
    Forecast.canonicalFanningForecastAuthorityBoundary ≡ false
aiccDoesNotBecomeCrossFamilyAuthority = refl

bauDoesNotBecomeObservation :
  Forecast.bauMedianIsObservedFuture
    Forecast.canonicalFanningForecastAuthorityBoundary ≡ false
bauDoesNotBecomeObservation = refl
