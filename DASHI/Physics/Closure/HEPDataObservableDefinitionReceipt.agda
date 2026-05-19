module DASHI.Physics.Closure.HEPDataObservableDefinitionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- HEP-R45: local HEPData observable-definition receipt.
--
-- This module records the local CSV header facts for the t43/t44 and t45/t46
-- phistar ratio surfaces.  It is a non-promoting receipt surface only: it
-- defines no accepted authority token, no prediction freeze, no comparison
-- law, no calibration receipt, and no W3/W4/W5/W8 promotion.
--
-- Critical interpretation bound here:
--
--   t43/t45 are ratios of measured differential cross sections,
--   DSIG/DPHISTAR / DSIG/DPHISTAR.
--
-- The local headers explicitly say the values are not normalized by bin width.
-- This receipt also blocks the stronger normalized-by-total-cross-section
-- hypothesis, because that hypothesis is not the local header definition.

data HEPDataObservableDefinitionReceiptStatus : Set where
  localT43T44T45T46HeaderFactsRecordedNoPromotion :
    HEPDataObservableDefinitionReceiptStatus

data HEPDataObservableDefinitionTableRole : Set where
  ratioValueTableT43 :
    HEPDataObservableDefinitionTableRole
  ratioCovarianceTableT44 :
    HEPDataObservableDefinitionTableRole
  ratioValueTableT45 :
    HEPDataObservableDefinitionTableRole
  ratioCovarianceTableT46 :
    HEPDataObservableDefinitionTableRole

data HEPDataObservableDefinitionNormalizationFact : Set where
  notNormalizedByBinWidth :
    HEPDataObservableDefinitionNormalizationFact
  notNormalizedByTotalCrossSection :
    HEPDataObservableDefinitionNormalizationFact
  differentialCrossSectionRatio :
    HEPDataObservableDefinitionNormalizationFact

canonicalHEPDataObservableDefinitionNormalizationFacts :
  List HEPDataObservableDefinitionNormalizationFact
canonicalHEPDataObservableDefinitionNormalizationFacts =
  notNormalizedByBinWidth
  ∷ notNormalizedByTotalCrossSection
  ∷ differentialCrossSectionRatio
  ∷ []

data HEPDataObservableDefinitionRejectedHypothesis : Set where
  normalizedByTotalCrossSectionHypothesisBlocked :
    HEPDataObservableDefinitionRejectedHypothesis
  normalizedCrossSectionTableFamilyConfusionBlocked :
    HEPDataObservableDefinitionRejectedHypothesis

canonicalHEPDataObservableDefinitionRejectedHypotheses :
  List HEPDataObservableDefinitionRejectedHypothesis
canonicalHEPDataObservableDefinitionRejectedHypotheses =
  normalizedByTotalCrossSectionHypothesisBlocked
  ∷ normalizedCrossSectionTableFamilyConfusionBlocked
  ∷ []

record HEPDataObservableDefinitionHeaderFact : Set where
  field
    role :
      HEPDataObservableDefinitionTableRole

    tableDOI :
      String

    tableName :
      String

    localPath :
      String

    headerDescription :
      String

    dataFile :
      String

    observableKeyword :
      String

    numeratorMassWindow :
      String

    denominatorMassWindow :
      String

    ratioConvention :
      String

    normalizedByBinWidth :
      Bool

    normalizedByBinWidthIsFalse :
      normalizedByBinWidth ≡ false

    normalizedByTotalCrossSection :
      Bool

    normalizedByTotalCrossSectionIsFalse :
      normalizedByTotalCrossSection ≡ false

canonicalT43ObservableDefinitionHeaderFact :
  HEPDataObservableDefinitionHeaderFact
canonicalT43ObservableDefinitionHeaderFact =
  record
    { role =
        ratioValueTableT43
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t43"
    ; tableName =
        "phistar mass 50-76 over mass 76-106"
    ; localPath =
        "scripts/data/hepdata/ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv"
    ; headerDescription =
        "The measured differential cross section in the 50<=Mll<76 GeV mass window, in bins of the phistar variable, divided by the measured differential cross section in the 76<=Mll<106 GeV mass window. At least one jet is required. The values are not normalized by the bin width."
    ; dataFile =
        "phistar_mass_50-76_over_mass_76-106.yaml"
    ; observableKeyword =
        "DSIG/DPHISTAR / DSIG/DPHISTAR"
    ; numeratorMassWindow =
        "50<=Mll<76 GeV"
    ; denominatorMassWindow =
        "76<=Mll<106 GeV"
    ; ratioConvention =
        "measured differential cross section in numerator mass window divided by measured differential cross section in denominator mass window"
    ; normalizedByBinWidth =
        false
    ; normalizedByBinWidthIsFalse =
        refl
    ; normalizedByTotalCrossSection =
        false
    ; normalizedByTotalCrossSectionIsFalse =
        refl
    }

canonicalT44ObservableDefinitionHeaderFact :
  HEPDataObservableDefinitionHeaderFact
canonicalT44ObservableDefinitionHeaderFact =
  record
    { role =
        ratioCovarianceTableT44
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t44"
    ; tableName =
        "Covariance matrices for phistar mass 50-76 over mass 76-106"
    ; localPath =
        "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_over_mass_76-106_t44.csv"
    ; headerDescription =
        "The measured differential cross section in the 50<=Mll<76 GeV mass window, in bins of the phistar variable, divided by the measured differential cross section in the 76<=Mll<106 GeV mass window. At least one jet is required. The values are not normalized by the bin width. This entry contains the covariance matrix of the results."
    ; dataFile =
        "covariance_matrices_for_phistar_mass_50-76_over_mass_76-106.yaml"
    ; observableKeyword =
        "DSIG/DPHISTAR / DSIG/DPHISTAR"
    ; numeratorMassWindow =
        "50<=Mll<76 GeV"
    ; denominatorMassWindow =
        "76<=Mll<106 GeV"
    ; ratioConvention =
        "covariance matrix for the t43 differential-cross-section ratio results"
    ; normalizedByBinWidth =
        false
    ; normalizedByBinWidthIsFalse =
        refl
    ; normalizedByTotalCrossSection =
        false
    ; normalizedByTotalCrossSectionIsFalse =
        refl
    }

canonicalT45ObservableDefinitionHeaderFact :
  HEPDataObservableDefinitionHeaderFact
canonicalT45ObservableDefinitionHeaderFact =
  record
    { role =
        ratioValueTableT45
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t45"
    ; tableName =
        "phistar mass 106-170 over mass 76-106"
    ; localPath =
        "scripts/data/hepdata/ins2079374_phistar_mass_106-170_over_mass_76-106_t45.csv"
    ; headerDescription =
        "The measured differential cross section in the 106<=Mll<170 GeV mass window, in bins of the phistar variable, divided by the measured differential cross section in the 76<=Mll<106 GeV mass window. At least one jet is required. The values are not normalized by the bin width."
    ; dataFile =
        "phistar_mass_106-170_over_mass_76-106.yaml"
    ; observableKeyword =
        "DSIG/DPHISTAR / DSIG/DPHISTAR"
    ; numeratorMassWindow =
        "106<=Mll<170 GeV"
    ; denominatorMassWindow =
        "76<=Mll<106 GeV"
    ; ratioConvention =
        "measured differential cross section in numerator mass window divided by measured differential cross section in denominator mass window"
    ; normalizedByBinWidth =
        false
    ; normalizedByBinWidthIsFalse =
        refl
    ; normalizedByTotalCrossSection =
        false
    ; normalizedByTotalCrossSectionIsFalse =
        refl
    }

canonicalT46ObservableDefinitionHeaderFact :
  HEPDataObservableDefinitionHeaderFact
canonicalT46ObservableDefinitionHeaderFact =
  record
    { role =
        ratioCovarianceTableT46
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t46"
    ; tableName =
        "Covariance matrices for phistar mass 106-170 over mass 76-106"
    ; localPath =
        "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_106-170_over_mass_76-106_t46.csv"
    ; headerDescription =
        "The measured differential cross section in the 106<=Mll<170 GeV mass window, in bins of the phistar variable, divided by the measured differential cross section in the 76<=Mll<106 GeV mass window. At least one jet is required. The values are not normalized by the bin width. This entry contains the covariance matrix of the results."
    ; dataFile =
        "covariance_matrices_for_phistar_mass_106-170_over_mass_76-106.yaml"
    ; observableKeyword =
        "DSIG/DPHISTAR / DSIG/DPHISTAR"
    ; numeratorMassWindow =
        "106<=Mll<170 GeV"
    ; denominatorMassWindow =
        "76<=Mll<106 GeV"
    ; ratioConvention =
        "covariance matrix for the t45 differential-cross-section ratio results"
    ; normalizedByBinWidth =
        false
    ; normalizedByBinWidthIsFalse =
        refl
    ; normalizedByTotalCrossSection =
        false
    ; normalizedByTotalCrossSectionIsFalse =
        refl
    }

canonicalHEPDataObservableDefinitionHeaderFacts :
  List HEPDataObservableDefinitionHeaderFact
canonicalHEPDataObservableDefinitionHeaderFacts =
  canonicalT43ObservableDefinitionHeaderFact
  ∷ canonicalT44ObservableDefinitionHeaderFact
  ∷ canonicalT45ObservableDefinitionHeaderFact
  ∷ canonicalT46ObservableDefinitionHeaderFact
  ∷ []

data HEPDataObservableDefinitionBoundary : Set where
  localHeaderReceiptOnly :
    HEPDataObservableDefinitionBoundary
  noCSVValueParsingHere :
    HEPDataObservableDefinitionBoundary
  noPredictionFreezeHere :
    HEPDataObservableDefinitionBoundary
  noProjectionRunHere :
    HEPDataObservableDefinitionBoundary
  noComparisonLawHere :
    HEPDataObservableDefinitionBoundary
  noCalibrationReceiptHere :
    HEPDataObservableDefinitionBoundary
  noW3W4W5W8PromotionHere :
    HEPDataObservableDefinitionBoundary

canonicalHEPDataObservableDefinitionBoundaries :
  List HEPDataObservableDefinitionBoundary
canonicalHEPDataObservableDefinitionBoundaries =
  localHeaderReceiptOnly
  ∷ noCSVValueParsingHere
  ∷ noPredictionFreezeHere
  ∷ noProjectionRunHere
  ∷ noComparisonLawHere
  ∷ noCalibrationReceiptHere
  ∷ noW3W4W5W8PromotionHere
  ∷ []

data HEPDataObservableDefinitionPromotionReceipt : Set where

hepR45PromotionReceiptImpossibleHere :
  HEPDataObservableDefinitionPromotionReceipt →
  ⊥
hepR45PromotionReceiptImpossibleHere ()

data HEPDataNormalizedByTotalCrossSectionReceipt : Set where

hepR45NormalizedByTotalCrossSectionReceiptImpossibleHere :
  HEPDataNormalizedByTotalCrossSectionReceipt →
  ⊥
hepR45NormalizedByTotalCrossSectionReceiptImpossibleHere ()

record HEPDataObservableDefinitionReceipt : Setω where
  field
    status :
      HEPDataObservableDefinitionReceiptStatus

    headerFacts :
      List HEPDataObservableDefinitionHeaderFact

    headerFactsAreCanonical :
      headerFacts
      ≡
      canonicalHEPDataObservableDefinitionHeaderFacts

    normalizationFacts :
      List HEPDataObservableDefinitionNormalizationFact

    normalizationFactsAreCanonical :
      normalizationFacts
      ≡
      canonicalHEPDataObservableDefinitionNormalizationFacts

    t43Name :
      String

    t43NameIsCanonical :
      t43Name
      ≡
      "phistar mass 50-76 over mass 76-106"

    t45Name :
      String

    t45NameIsCanonical :
      t45Name
      ≡
      "phistar mass 106-170 over mass 76-106"

    observableKeyword :
      String

    observableKeywordIsCanonical :
      observableKeyword
      ≡
      "DSIG/DPHISTAR / DSIG/DPHISTAR"

    t43NumeratorMassWindow :
      String

    t43NumeratorMassWindowIsCanonical :
      t43NumeratorMassWindow
      ≡
      "50<=Mll<76 GeV"

    t45NumeratorMassWindow :
      String

    t45NumeratorMassWindowIsCanonical :
      t45NumeratorMassWindow
      ≡
      "106<=Mll<170 GeV"

    sharedDenominatorMassWindow :
      String

    sharedDenominatorMassWindowIsCanonical :
      sharedDenominatorMassWindow
      ≡
      "76<=Mll<106 GeV"

    normalizedByBinWidth :
      Bool

    normalizedByBinWidthIsFalse :
      normalizedByBinWidth ≡ false

    normalizedByTotalCrossSection :
      Bool

    normalizedByTotalCrossSectionIsFalse :
      normalizedByTotalCrossSection ≡ false

    normalizedByTotalCrossSectionHypotheses :
      List HEPDataObservableDefinitionRejectedHypothesis

    normalizedByTotalCrossSectionHypothesesAreCanonical :
      normalizedByTotalCrossSectionHypotheses
      ≡
      canonicalHEPDataObservableDefinitionRejectedHypotheses

    localHeaderFactsValidated :
      Bool

    localHeaderFactsValidatedIsTrue :
      localHeaderFactsValidated ≡ true

    receiptNotes :
      List String

    boundaries :
      List HEPDataObservableDefinitionBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataObservableDefinitionBoundaries

    normalizedByTotalCrossSectionReceiptBlocked :
      HEPDataNormalizedByTotalCrossSectionReceipt →
      ⊥

    promotionReceiptBlocked :
      HEPDataObservableDefinitionPromotionReceipt →
      ⊥

canonicalHEPDataObservableDefinitionReceipt :
  HEPDataObservableDefinitionReceipt
canonicalHEPDataObservableDefinitionReceipt =
  record
    { status =
        localT43T44T45T46HeaderFactsRecordedNoPromotion
    ; headerFacts =
        canonicalHEPDataObservableDefinitionHeaderFacts
    ; headerFactsAreCanonical =
        refl
    ; normalizationFacts =
        canonicalHEPDataObservableDefinitionNormalizationFacts
    ; normalizationFactsAreCanonical =
        refl
    ; t43Name =
        "phistar mass 50-76 over mass 76-106"
    ; t43NameIsCanonical =
        refl
    ; t45Name =
        "phistar mass 106-170 over mass 76-106"
    ; t45NameIsCanonical =
        refl
    ; observableKeyword =
        "DSIG/DPHISTAR / DSIG/DPHISTAR"
    ; observableKeywordIsCanonical =
        refl
    ; t43NumeratorMassWindow =
        "50<=Mll<76 GeV"
    ; t43NumeratorMassWindowIsCanonical =
        refl
    ; t45NumeratorMassWindow =
        "106<=Mll<170 GeV"
    ; t45NumeratorMassWindowIsCanonical =
        refl
    ; sharedDenominatorMassWindow =
        "76<=Mll<106 GeV"
    ; sharedDenominatorMassWindowIsCanonical =
        refl
    ; normalizedByBinWidth =
        false
    ; normalizedByBinWidthIsFalse =
        refl
    ; normalizedByTotalCrossSection =
        false
    ; normalizedByTotalCrossSectionIsFalse =
        refl
    ; normalizedByTotalCrossSectionHypotheses =
        canonicalHEPDataObservableDefinitionRejectedHypotheses
    ; normalizedByTotalCrossSectionHypothesesAreCanonical =
        refl
    ; localHeaderFactsValidated =
        true
    ; localHeaderFactsValidatedIsTrue =
        refl
    ; receiptNotes =
        "HEP-R45 records local CSV header semantics only for t43/t44 and t45/t46"
        ∷ "t43 is 50<=Mll<76 over 76<=Mll<106 using DSIG/DPHISTAR / DSIG/DPHISTAR"
        ∷ "t45 is 106<=Mll<170 over 76<=Mll<106 using the same convention"
        ∷ "The local headers say values are not normalized by bin width"
        ∷ "The normalized-by-total-cross-section hypothesis is explicitly blocked here"
        ∷ "No W3, W4, W5, or W8 promotion is constructed by this receipt"
        ∷ []
    ; boundaries =
        canonicalHEPDataObservableDefinitionBoundaries
    ; boundariesAreCanonical =
        refl
    ; normalizedByTotalCrossSectionReceiptBlocked =
        hepR45NormalizedByTotalCrossSectionReceiptImpossibleHere
    ; promotionReceiptBlocked =
        hepR45PromotionReceiptImpossibleHere
    }

canonicalHEPDataObservableDefinitionReceiptStatus :
  HEPDataObservableDefinitionReceiptStatus
canonicalHEPDataObservableDefinitionReceiptStatus =
  HEPDataObservableDefinitionReceipt.status
    canonicalHEPDataObservableDefinitionReceipt
