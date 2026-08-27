module DASHI.Governance.Fanning2022MissingnessAndBalancedSampleExact where

open import DASHI.Core.Prelude
import DASHI.Governance.SafeJustSourceRegistryExact as Sources

data CoverageRole : Set where
  fullVocabulary longPeriodComparable shortWindowSummary balancedHistoricalPath : CoverageRole

socialVocabularyCount longPeriodSocialCount balancedRequiredSocialCount : Nat
socialVocabularyCount = 11
longPeriodSocialCount = 10
balancedRequiredSocialCount = 9

biophysicalRequiredCount balancedCountryCount : Nat
biophysicalRequiredCount = 6
balancedCountryCount = 91

summaryStart summaryEnd historicalStart historicalEnd socialSupportStart : Nat
summaryStart = 2005
summaryEnd = 2015
historicalStart = 1992
historicalEnd = 2015
socialSupportStart = 2005

data DataCoverageResidual : Set where
  noLongitudinalBlueWaterSeries socialSupportBeginsIn2005 heterogeneousSocialCoverage : DataCoverageResidual

record CoverageResidualWitness : Set where
  constructor coverageResidualWitness
  field
    residual : DataCoverageResidual
    representedAsZeroPhenomenonResidual : Bool
    representedAsSatisfiedThreshold : Bool

socialSupportCoverageResidual : CoverageResidualWitness
socialSupportCoverageResidual = coverageResidualWitness socialSupportBeginsIn2005 false false

source : Sources.SourceReference
source = Sources.fanning2022

record FanningMissingnessBalancedSampleBoundary : Set where
  constructor fanningMissingnessBalancedSampleBoundary
  field
    overallSocialVocabulary : Nat
    overallSocialVocabularyIsEleven : overallSocialVocabulary ≡ 11
    longPeriodCrossNationalSocialIndicators : Nat
    longPeriodCrossNationalSocialIndicatorsAreTen : longPeriodCrossNationalSocialIndicators ≡ 10
    balancedPathRequiresAllSixBiophysical : Bool
    balancedPathRequiresAllSixBiophysicalIsTrue : balancedPathRequiresAllSixBiophysical ≡ true
    balancedPathRequiresAtLeastNineOfTenSocial : Bool
    balancedPathRequiresAtLeastNineOfTenSocialIsTrue : balancedPathRequiresAtLeastNineOfTenSocial ≡ true
    balancedHistoricalCountries : Nat
    balancedHistoricalCountriesAreNinetyOne : balancedHistoricalCountries ≡ 91
    aggregateSummaryWindowStarts2005 : Bool
    aggregateSummaryWindowStarts2005IsTrue : aggregateSummaryWindowStarts2005 ≡ true
    missingCoordinateMeansZeroResidual : Bool
    missingCoordinateMeansZeroResidualIsFalse : missingCoordinateMeansZeroResidual ≡ false
    missingCoordinateMeansThresholdSatisfied : Bool
    missingCoordinateMeansThresholdSatisfiedIsFalse : missingCoordinateMeansThresholdSatisfied ≡ false

canonicalFanningMissingnessBalancedSampleBoundary : FanningMissingnessBalancedSampleBoundary
canonicalFanningMissingnessBalancedSampleBoundary =
  fanningMissingnessBalancedSampleBoundary 11 refl 10 refl true refl true refl 91 refl true refl false refl false refl
