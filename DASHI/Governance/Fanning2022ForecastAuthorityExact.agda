module DASHI.Governance.Fanning2022ForecastAuthorityExact where

open import DASHI.Core.Prelude
import DASHI.Governance.Fanning2022TemporalIndicatorExact as Temporal
import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- FANNING ET AL. 2022: BAU FORECAST MODEL-SELECTION AUTHORITY
--
-- For each country and each of the 17 indicator time series (11 social + 6
-- biophysical), the paper considers ETS and ARIMA forecasting families.
-- Parameters are selected WITHIN each family by minimizing AICc.  AICc is not
-- used to compare ETS against ARIMA because the likelihood calculations differ
-- across the two model classes.  Cross-family selection is therefore performed
-- by time-series cross-validation, minimizing the paper's stated "mean standard
-- error" criterion.  The selected model supplies the BAU projection to 2050 and
-- its 66% prediction interval.
--
-- The types below mirror PR #615's proof-carrying authority lesson: a family
-- label is not itself a certificate that the family won the appropriate
-- selection stage.  Within-family and cross-family authority remain separate.
------------------------------------------------------------------------

data ForecastFamily : Set where
  ets arima : ForecastFamily

data SelectionCriterion : Set where
  aicc timeSeriesCrossValidationMeanStandardError : SelectionCriterion

record WithinFamilySelection : Set where
  constructor withinFamilySelection
  field
    family : ForecastFamily
    criterion : SelectionCriterion
    usesAICc : criterion ≡ aicc
    parameterChoiceCode : Nat

open WithinFamilySelection public

record CrossFamilySelection : Set where
  constructor crossFamilySelection
  field
    etsWinner : WithinFamilySelection
    arimaWinner : WithinFamilySelection
    etsFamilyCorrect : family etsWinner ≡ ets
    arimaFamilyCorrect : family arimaWinner ≡ arima
    criterion : SelectionCriterion
    usesTimeSeriesCrossValidation :
      criterion ≡ timeSeriesCrossValidationMeanStandardError
    chosenFamily : ForecastFamily

open CrossFamilySelection public

canonicalETSSelection : WithinFamilySelection
canonicalETSSelection = withinFamilySelection ets aicc refl 0

canonicalARIMASelection : WithinFamilySelection
canonicalARIMASelection = withinFamilySelection arima aicc refl 0

canonicalCrossFamilySelection : CrossFamilySelection
canonicalCrossFamilySelection =
  crossFamilySelection
    canonicalETSSelection
    canonicalARIMASelection
    refl refl
    timeSeriesCrossValidationMeanStandardError refl
    ets

------------------------------------------------------------------------
-- Projection output authority.
------------------------------------------------------------------------

record BAUProjectionReceipt : Set where
  constructor bauProjectionReceipt
  field
    selection : CrossFamilySelection
    evidenceRole : Temporal.TemporalEvidenceRole
    isProjection : evidenceRole ≡ Temporal.businessAsUsualProjection
    centralEstimateCode : Nat
    lower66Code : Nat
    upper66Code : Nat

open BAUProjectionReceipt public

canonicalProjectionReceipt : BAUProjectionReceipt
canonicalProjectionReceipt =
  bauProjectionReceipt canonicalCrossFamilySelection
    Temporal.businessAsUsualProjection refl 100 80 120

------------------------------------------------------------------------
-- Source-scale metadata.  "More than 100,000" is retained as a lower-bound
-- claim rather than silently converted into an exact count.
------------------------------------------------------------------------

indicatorTimeSeriesPerCountry : Nat
indicatorTimeSeriesPerCountry = 17

forecastCountryCount : Nat
forecastCountryCount = 148

parameterCombinationStrictLowerBound : Nat
parameterCombinationStrictLowerBound = 100000

record ForecastScaleBoundary : Set where
  constructor forecastScaleBoundary
  field
    indicatorsPerCountry : Nat
    indicatorsPerCountryAreSeventeen : indicatorsPerCountry ≡ 17
    countries : Nat
    countriesAreOneFortyEight : countries ≡ 148
    parameterCombinationsExceedOneHundredThousand : Bool
    parameterCombinationsExceedOneHundredThousandIsTrue :
      parameterCombinationsExceedOneHundredThousand ≡ true

canonicalForecastScaleBoundary : ForecastScaleBoundary
canonicalForecastScaleBoundary = forecastScaleBoundary 17 refl 148 refl true refl

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

data CausalForecastMechanism : Set where

data Observed2050Outcome : Set where

projectionDoesNotSupplyCausalMechanism : CausalForecastMechanism → ⊥
projectionDoesNotSupplyCausalMechanism ()

projectionDoesNotSupplyObserved2050Outcome : Observed2050Outcome → ⊥
projectionDoesNotSupplyObserved2050Outcome ()

source : Sources.SourceReference
source = Sources.fanning2022

record FanningForecastAuthorityBoundary : Set where
  constructor fanningForecastAuthorityBoundary
  field
    aiccSelectsParametersWithinETS : Bool
    aiccSelectsParametersWithinETSIsTrue : aiccSelectsParametersWithinETS ≡ true
    aiccSelectsParametersWithinARIMA : Bool
    aiccSelectsParametersWithinARIMAIsTrue : aiccSelectsParametersWithinARIMA ≡ true
    aiccIsValidCrossFamilyETSARIMAComparison : Bool
    aiccIsValidCrossFamilyETSARIMAComparisonIsFalse :
      aiccIsValidCrossFamilyETSARIMAComparison ≡ false
    crossFamilyChoiceUsesTimeSeriesCrossValidation : Bool
    crossFamilyChoiceUsesTimeSeriesCrossValidationIsTrue :
      crossFamilyChoiceUsesTimeSeriesCrossValidation ≡ true
    crossValidatedBestFitIsCausalMechanism : Bool
    crossValidatedBestFitIsCausalMechanismIsFalse :
      crossValidatedBestFitIsCausalMechanism ≡ false
    bauMedianIsObservedFuture : Bool
    bauMedianIsObservedFutureIsFalse : bauMedianIsObservedFuture ≡ false
    sixtySixPredictionIntervalIsDeterministicBound : Bool
    sixtySixPredictionIntervalIsDeterministicBoundIsFalse :
      sixtySixPredictionIntervalIsDeterministicBound ≡ false
    indicatorWiseForecastsFormJointCausalSystem : Bool
    indicatorWiseForecastsFormJointCausalSystemIsFalse :
      indicatorWiseForecastsFormJointCausalSystem ≡ false

canonicalFanningForecastAuthorityBoundary : FanningForecastAuthorityBoundary
canonicalFanningForecastAuthorityBoundary =
  fanningForecastAuthorityBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
