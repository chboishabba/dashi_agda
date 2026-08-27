module DASHI.Governance.Fanning2022TemporalIndicatorExact where

open import DASHI.Core.Prelude
open import DASHI.Governance.SafeJustIndicatorSystemExact as ONeill
open import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- FANNING ET AL. 2022: TEMPORAL / INDICATOR AUTHORITY BOUNDARY
--
-- Andrew L. Fanning, Daniel W. O'Neill, Jason Hickel, Nicolas Roux,
-- "The social shortfall and ecological overshoot of nations",
-- Nature Sustainability 5, 26--36 (2022).
-- DOI: 10.1038/s41893-021-00799-z.
--
-- The 2022 paper extends the 2018 safe-and-just programme through time, but it
-- does NOT simply reuse an identical 7 x 11 national panel.  At national scale
-- it analyses six biophysical indicators over 1992--2015.  Blue-water footprint
-- lacks a suitable country time series and is therefore not one of those six.
-- The social vocabulary remains eleven indicators, while temporal coverage is
-- indicator-dependent (not every cross-country summary has all eleven at every
-- year).  BAU projections extend from 2016 to 2050.
------------------------------------------------------------------------

data FanningNationalBiophysicalIndicator : Set where
  co2F phosphorusF nitrogenF landSystemChangeF ecologicalFootprintF materialFootprintF :
    FanningNationalBiophysicalIndicator

fanningToONeillBiophysical :
  FanningNationalBiophysicalIndicator → ONeill.BiophysicalIndicator
fanningToONeillBiophysical co2F = ONeill.co2Emissions
fanningToONeillBiophysical phosphorusF = ONeill.phosphorus
fanningToONeillBiophysical nitrogenF = ONeill.nitrogen
fanningToONeillBiophysical landSystemChangeF = ONeill.eHANPP
fanningToONeillBiophysical ecologicalFootprintF = ONeill.ecologicalFootprint
fanningToONeillBiophysical materialFootprintF = ONeill.materialFootprint

fanningNationalBiophysicalCount : Nat
fanningNationalBiophysicalCount = 6

fanningSocialVocabularyCount : Nat
fanningSocialVocabularyCount = 11

historicalStart historicalEnd projectionStart projectionEnd : Nat
historicalStart = 1992
historicalEnd = 2015
projectionStart = 2016
projectionEnd = 2050

data TemporalEvidenceRole : Set where
  historicalObservation businessAsUsualProjection : TemporalEvidenceRole

data ProjectionBandRole : Set where
  centralProjection lower66 upper66 : ProjectionBandRole

source : Sources.SourceReference
source = Sources.fanning2022

------------------------------------------------------------------------
-- Exact source-scope boundaries.
------------------------------------------------------------------------

record FanningTemporalIndicatorBoundary : Set where
  constructor fanningTemporalIndicatorBoundary
  field
    nationalBiophysicalIndicators : Nat
    nationalBiophysicalIndicatorsAreSix : nationalBiophysicalIndicators ≡ 6
    socialVocabularyIndicators : Nat
    socialVocabularyIndicatorsAreEleven : socialVocabularyIndicators ≡ 11
    blueWaterIsIn2018BiophysicalVocabulary : Bool
    blueWaterIsIn2018BiophysicalVocabularyIsTrue :
      blueWaterIsIn2018BiophysicalVocabulary ≡ true
    blueWaterHasSuitableNational1992To2015TimeSeries : Bool
    blueWaterHasSuitableNational1992To2015TimeSeriesIsFalse :
      blueWaterHasSuitableNational1992To2015TimeSeries ≡ false
    allSocialIndicatorsHaveIdenticalTemporalCoverage : Bool
    allSocialIndicatorsHaveIdenticalTemporalCoverageIsFalse :
      allSocialIndicatorsHaveIdenticalTemporalCoverage ≡ false
    historicalObservationIsBAUProjection : Bool
    historicalObservationIsBAUProjectionIsFalse :
      historicalObservationIsBAUProjection ≡ false
    nationalSixIndicatorPanelEqualsGlobalSevenBoundaryDisplay : Bool
    nationalSixIndicatorPanelEqualsGlobalSevenBoundaryDisplayIsFalse :
      nationalSixIndicatorPanelEqualsGlobalSevenBoundaryDisplay ≡ false

canonicalFanningTemporalIndicatorBoundary : FanningTemporalIndicatorBoundary
canonicalFanningTemporalIndicatorBoundary =
  fanningTemporalIndicatorBoundary
    6 refl
    11 refl
    true refl
    false refl
    false refl
    false refl
    false refl
