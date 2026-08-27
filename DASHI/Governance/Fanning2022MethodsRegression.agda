module DASHI.Governance.Fanning2022MethodsRegression where

open import DASHI.Core.Prelude
import DASHI.Governance.Fanning2022TemporalIndicatorExact as Temporal
import DASHI.Governance.Fanning2022SocialIndicatorRevisionExact as SocialRevision
import DASHI.Governance.Fanning2022NormalizationExact as Normalization
import DASHI.Governance.Fanning2022ProjectionBoundaryExact as Projection
import DASHI.Governance.Fanning2022ForecastAuthorityExact as Forecast
import DASHI.Governance.Fanning2022MissingnessAndBalancedSampleExact as Missingness
import DASHI.Governance.Fanning2022DataRealizationExact as Data

nationalBioCountReceipt : Temporal.fanningNationalBiophysicalCount ≡ 6
nationalBioCountReceipt = refl

socialVocabularyCountReceipt : Temporal.fanningSocialVocabularyCount ≡ 11
socialVocabularyCountReceipt = refl

longevityMeasurementRevisionReceipt :
  SocialRevision.healthyLifeExpectancy ≡ SocialRevision.overallLifeExpectancy → ⊥
longevityMeasurementRevisionReceipt = SocialRevision.earlierAndLongitudinalLongevityMeasuresDiffer

povertyThresholdRevisionReceipt :
  SocialRevision.extremePoverty190 ≡ SocialRevision.broaderPoverty550 → ⊥
povertyThresholdRevisionReceipt = SocialRevision.earlierAndLongitudinalPovertyLinesDiffer

normalizationAuthoritySeparation :
  Normalization.biophysicalNormalizationAuthority ≡ Normalization.socialNormalizationAuthority → ⊥
normalizationAuthoritySeparation = Normalization.normalizationAuthoritiesDiffer

socialShortfallClippingReceipt : Normalization.socialShortfallComponent 70 ≡ 30
socialShortfallClippingReceipt = refl

ecologicalOvershootClippingReceipt : Normalization.ecologicalOvershootComponent 130 ≡ 30
ecologicalOvershootClippingReceipt = refl

withinDomainCompensationCollision : Normalization.withinDomainA ≡ Normalization.withinDomainB
withinDomainCompensationCollision = Normalization.sameWithinDomainAverageCode

crossDomainScalarCollision :
  Normalization.combinedNumerator Normalization.socialHeavy ≡ Normalization.combinedNumerator Normalization.ecoHeavy
crossDomainScalarCollision = Normalization.sameCombinedNumerator

countDoesNotBecomeExtent :
  Projection.countViewEqualsExtentView Projection.canonicalFanningProjectionBoundary ≡ false
countDoesNotBecomeExtent = refl

forecastIndicatorCountReceipt : Forecast.indicatorTimeSeriesPerCountry ≡ 17
forecastIndicatorCountReceipt = refl

forecastCountryCountReceipt : Forecast.forecastCountryCount ≡ 148
forecastCountryCountReceipt = refl

aiccDoesNotBecomeCrossFamilyAuthority :
  Forecast.aiccIsValidCrossFamilyETSARIMAComparison Forecast.canonicalFanningForecastAuthorityBoundary ≡ false
aiccDoesNotBecomeCrossFamilyAuthority = refl

bauDoesNotBecomeObservation :
  Forecast.bauMedianIsObservedFuture Forecast.canonicalFanningForecastAuthorityBoundary ≡ false
bauDoesNotBecomeObservation = refl

longPeriodUsesTenSocialReceipt : Missingness.longPeriodSocialCount ≡ 10
longPeriodUsesTenSocialReceipt = refl

balancedSampleRequiresNineReceipt : Missingness.balancedRequiredSocialCount ≡ 9
balancedSampleRequiresNineReceipt = refl

balancedSampleNReceipt : Missingness.balancedCountryCount ≡ 91
balancedSampleNReceipt = refl

summaryWindowReceipt : Missingness.summaryStart ≡ 2005
summaryWindowReceipt = refl

observationProjectionAuthoritySeparation :
  Data.observedDatum ≡ Data.projectedMedian → ⊥
observationProjectionAuthoritySeparation = Data.observationAuthorityDiffersFromProjection
