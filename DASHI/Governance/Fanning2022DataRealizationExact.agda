module DASHI.Governance.Fanning2022DataRealizationExact where

open import DASHI.Core.Prelude
import DASHI.Governance.Fanning2022TemporalIndicatorExact as Temporal
import DASHI.Governance.Fanning2022MissingnessAndBalancedSampleExact as Missingness
import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- Typed realization surface for the published country/year/indicator data.
-- This module owns the shape and provenance of observations and projections;
-- it does not fabricate the full spreadsheet inside Agda.
------------------------------------------------------------------------

data Country : Set where
  countryCode : Nat → Country

data SocialSeries : Set where
  socialSeries : Nat → SocialSeries

data IndicatorRole : Set where
  biophysicalRole : Temporal.FanningNationalBiophysicalIndicator → IndicatorRole
  socialRole : SocialSeries → IndicatorRole

data DatumAuthority : Set where
  observedDatum projectedMedian projectedLower66 projectedUpper66 : DatumAuthority

record CountryYearDatum : Set where
  constructor countryYearDatum
  field
    country : Country
    year : Nat
    indicator : IndicatorRole
    valueCode : Nat
    authority : DatumAuthority

historicalDatum : Country → Nat → IndicatorRole → Nat → CountryYearDatum
historicalDatum c y i v = countryYearDatum c y i v observedDatum

projectedDatum : Country → Nat → IndicatorRole → Nat → DatumAuthority → CountryYearDatum
projectedDatum c y i v a = countryYearDatum c y i v a

record RealizationReceipt (d : CountryYearDatum) : Set where
  constructor realizationReceipt
  field
    sourcePresent : Bool
    authorityPreserved : Bool

record DataTransformationStage : Set where
  constructor dataTransformationStage
  field
    raw : CountryYearDatum
    normalizedCode : Nat
    residualCode : Nat
    aggregateNumerator : Nat
    aggregateCount : Nat

-- Observation and projection are distinct constructors of authority even when
-- year, indicator and numeric value happen to coincide.
observationAuthorityDiffersFromProjection : observedDatum ≡ projectedMedian → ⊥
observationAuthorityDiffersFromProjection ()

missingnessIsNotDatum :
  Missingness.DataCoverageResidual ≡ CountryYearDatum → ⊥
missingnessIsNotDatum ()

source : Sources.SourceReference
source = Sources.fanning2022

record FanningDataRealizationBoundary : Set where
  constructor fanningDataRealizationBoundary
  field
    dataCarrierHasCountryCoordinate : Bool
    dataCarrierHasCountryCoordinateIsTrue : dataCarrierHasCountryCoordinate ≡ true
    dataCarrierHasYearCoordinate : Bool
    dataCarrierHasYearCoordinateIsTrue : dataCarrierHasYearCoordinate ≡ true
    dataCarrierHasIndicatorCoordinate : Bool
    dataCarrierHasIndicatorCoordinateIsTrue : dataCarrierHasIndicatorCoordinate ≡ true
    observationEqualsProjectionAuthority : Bool
    observationEqualsProjectionAuthorityIsFalse : observationEqualsProjectionAuthority ≡ false
    missingCoverageIsNumericZeroDatum : Bool
    missingCoverageIsNumericZeroDatumIsFalse : missingCoverageIsNumericZeroDatum ≡ false
    fullSpreadsheetValuesReconstructedInThisModule : Bool
    fullSpreadsheetValuesReconstructedInThisModuleIsFalse : fullSpreadsheetValuesReconstructedInThisModule ≡ false

canonicalFanningDataRealizationBoundary : FanningDataRealizationBoundary
canonicalFanningDataRealizationBoundary =
  fanningDataRealizationBoundary true refl true refl true refl false refl false refl false refl
