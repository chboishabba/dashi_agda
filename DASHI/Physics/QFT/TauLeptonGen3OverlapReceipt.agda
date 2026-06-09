module DASHI.Physics.QFT.TauLeptonGen3OverlapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.D11D12LeptonLanesReceipt as D11D12
import DASHI.Physics.QFT.LeptonSectorGapReceipt as Gap

------------------------------------------------------------------------
-- D=-12 tau-lane generation-3 overlap receipt.
--
-- The D=-12 candidate is retained with both level conventions.  The level-6
-- route records tau-to-p3 overlap ratio 1/3; the level-12 route records
-- tau-to-p2 overlap ratio 1/4.  These are overlap diagnostics only, not a
-- tau, lepton, Yukawa, Standard Model, G_DHR ~= G_SM, or terminal promotion.

data TauLeptonGen3OverlapStatus : Set where
  tauLeptonGen3OverlapRatiosRecorded :
    TauLeptonGen3OverlapStatus

data TauLeptonGen3LevelConvention : Set where
  levelSixConvention :
    TauLeptonGen3LevelConvention

  levelTwelveConvention :
    TauLeptonGen3LevelConvention

data TauLeptonGen3OverlapBlocker : Set where
  levelConventionRetainedAsTwoRoutes :
    TauLeptonGen3OverlapBlocker

  overlapRatioDiagnosticOnly :
    TauLeptonGen3OverlapBlocker

  missingTauYukawaCarrierMap :
    TauLeptonGen3OverlapBlocker

  missingExactLeptonGenerationPromotion :
    TauLeptonGen3OverlapBlocker

canonicalTauLeptonGen3OverlapBlockers :
  List TauLeptonGen3OverlapBlocker
canonicalTauLeptonGen3OverlapBlockers =
  levelConventionRetainedAsTwoRoutes
  ∷ overlapRatioDiagnosticOnly
  ∷ missingTauYukawaCarrierMap
  ∷ missingExactLeptonGenerationPromotion
  ∷ []

data TauLeptonGen3OverlapPromotion : Set where

tauLeptonGen3OverlapPromotionImpossibleHere :
  TauLeptonGen3OverlapPromotion →
  ⊥
tauLeptonGen3OverlapPromotionImpossibleHere ()

levelConventionLabel : String
levelConventionLabel =
  "D=-12 is recorded with both level 6 and level 12 overlap conventions"

levelSixOverlapLabel : String
levelSixOverlapLabel =
  "level 6 route records tau-to-p3 overlap ratio 1/3"

levelTwelveOverlapLabel : String
levelTwelveOverlapLabel =
  "level 12 route records tau-to-p2 overlap ratio 1/4"

receiptBoundaryLabel : String
receiptBoundaryLabel =
  "D=-12 tau-lane overlaps are diagnostic only; exact lepton/quark/SM/G_DHR/terminal promotions remain false"

record TauLeptonGen3OverlapReceipt : Setω where
  field
    d11d12LeptonLanesReceipt :
      D11D12.D11D12LeptonLanesReceipt

    leptonSectorGapReceipt :
      Gap.LeptonSectorGapReceipt

    status :
      TauLeptonGen3OverlapStatus

    statusIsOverlapRatiosRecorded :
      status ≡ tauLeptonGen3OverlapRatiosRecorded

    discriminant :
      Gap.ClassNumberOneDiscriminant

    discriminantIsDMinusTwelve :
      discriminant ≡ Gap.D-12

    levelConventions :
      List TauLeptonGen3LevelConvention

    levelConventionsAreCanonical :
      levelConventions ≡ levelSixConvention ∷ levelTwelveConvention ∷ []

    levelConventionStatement :
      String

    levelConventionStatementIsCanonical :
      levelConventionStatement ≡ levelConventionLabel

    levelSix :
      Nat

    levelSixIsSix :
      levelSix ≡ 6

    levelTwelve :
      Nat

    levelTwelveIsTwelve :
      levelTwelve ≡ 12

    p3Level :
      Nat

    p3LevelIsThree :
      p3Level ≡ 3

    p2Level :
      Nat

    p2LevelIsFour :
      p2Level ≡ 4

    gcdLevelSixWithP3 :
      Nat

    gcdLevelSixWithP3IsThree :
      gcdLevelSixWithP3 ≡ 3

    tauToP3RatioNumerator :
      Nat

    tauToP3RatioNumeratorIsOne :
      tauToP3RatioNumerator ≡ 1

    tauToP3RatioDenominator :
      Nat

    tauToP3RatioDenominatorIsThree :
      tauToP3RatioDenominator ≡ 3

    tauToP3OverlapStatement :
      String

    tauToP3OverlapStatementIsCanonical :
      tauToP3OverlapStatement ≡ levelSixOverlapLabel

    gcdLevelTwelveWithP2 :
      Nat

    gcdLevelTwelveWithP2IsFour :
      gcdLevelTwelveWithP2 ≡ 4

    tauToP2RatioNumerator :
      Nat

    tauToP2RatioNumeratorIsOne :
      tauToP2RatioNumerator ≡ 1

    tauToP2RatioDenominator :
      Nat

    tauToP2RatioDenominatorIsFour :
      tauToP2RatioDenominator ≡ 4

    tauToP2OverlapStatement :
      String

    tauToP2OverlapStatementIsCanonical :
      tauToP2OverlapStatement ≡ levelTwelveOverlapLabel

    overlapRatiosRecorded :
      Bool

    overlapRatiosRecordedIsTrue :
      overlapRatiosRecorded ≡ true

    diagnosticOnly :
      Bool

    diagnosticOnlyIsTrue :
      diagnosticOnly ≡ true

    exactTauLeptonPromotion :
      Bool

    exactTauLeptonPromotionIsFalse :
      exactTauLeptonPromotion ≡ false

    exactLeptonPromotion :
      Bool

    exactLeptonPromotionIsFalse :
      exactLeptonPromotion ≡ false

    exactQuarkPromotion :
      Bool

    exactQuarkPromotionIsFalse :
      exactQuarkPromotion ≡ false

    exactYukawaPromotion :
      Bool

    exactYukawaPromotionIsFalse :
      exactYukawaPromotion ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    blockers :
      List TauLeptonGen3OverlapBlocker

    blockersAreCanonical :
      blockers ≡ canonicalTauLeptonGen3OverlapBlockers

    promotionFlags :
      List TauLeptonGen3OverlapPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryLabel

    auditTrail :
      List String

open TauLeptonGen3OverlapReceipt public

canonicalTauLeptonGen3OverlapReceipt :
  TauLeptonGen3OverlapReceipt
canonicalTauLeptonGen3OverlapReceipt =
  record
    { d11d12LeptonLanesReceipt =
        D11D12.canonicalD11D12LeptonLanesReceipt
    ; leptonSectorGapReceipt =
        Gap.canonicalLeptonSectorGapReceipt
    ; status =
        tauLeptonGen3OverlapRatiosRecorded
    ; statusIsOverlapRatiosRecorded =
        refl
    ; discriminant =
        Gap.D-12
    ; discriminantIsDMinusTwelve =
        refl
    ; levelConventions =
        levelSixConvention ∷ levelTwelveConvention ∷ []
    ; levelConventionsAreCanonical =
        refl
    ; levelConventionStatement =
        levelConventionLabel
    ; levelConventionStatementIsCanonical =
        refl
    ; levelSix =
        6
    ; levelSixIsSix =
        refl
    ; levelTwelve =
        12
    ; levelTwelveIsTwelve =
        refl
    ; p3Level =
        3
    ; p3LevelIsThree =
        refl
    ; p2Level =
        4
    ; p2LevelIsFour =
        refl
    ; gcdLevelSixWithP3 =
        3
    ; gcdLevelSixWithP3IsThree =
        refl
    ; tauToP3RatioNumerator =
        1
    ; tauToP3RatioNumeratorIsOne =
        refl
    ; tauToP3RatioDenominator =
        3
    ; tauToP3RatioDenominatorIsThree =
        refl
    ; tauToP3OverlapStatement =
        levelSixOverlapLabel
    ; tauToP3OverlapStatementIsCanonical =
        refl
    ; gcdLevelTwelveWithP2 =
        4
    ; gcdLevelTwelveWithP2IsFour =
        refl
    ; tauToP2RatioNumerator =
        1
    ; tauToP2RatioNumeratorIsOne =
        refl
    ; tauToP2RatioDenominator =
        4
    ; tauToP2RatioDenominatorIsFour =
        refl
    ; tauToP2OverlapStatement =
        levelTwelveOverlapLabel
    ; tauToP2OverlapStatementIsCanonical =
        refl
    ; overlapRatiosRecorded =
        true
    ; overlapRatiosRecordedIsTrue =
        refl
    ; diagnosticOnly =
        true
    ; diagnosticOnlyIsTrue =
        refl
    ; exactTauLeptonPromotion =
        false
    ; exactTauLeptonPromotionIsFalse =
        refl
    ; exactLeptonPromotion =
        false
    ; exactLeptonPromotionIsFalse =
        refl
    ; exactQuarkPromotion =
        false
    ; exactQuarkPromotionIsFalse =
        refl
    ; exactYukawaPromotion =
        false
    ; exactYukawaPromotionIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; blockers =
        canonicalTauLeptonGen3OverlapBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        receiptBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        levelConventionLabel
        ∷ levelSixOverlapLabel
        ∷ "gcd(6,3)=3 records the level-6 tau-to-p3 overlap carrier"
        ∷ levelTwelveOverlapLabel
        ∷ "gcd(12,4)=4 records the level-12 tau-to-p2 overlap carrier"
        ∷ receiptBoundaryLabel
        ∷ []
    }

tauLeptonGen3OverlapRecordsP3Ratio :
  tauToP3RatioDenominator canonicalTauLeptonGen3OverlapReceipt ≡ 3
tauLeptonGen3OverlapRecordsP3Ratio =
  refl

tauLeptonGen3OverlapRecordsP2Ratio :
  tauToP2RatioDenominator canonicalTauLeptonGen3OverlapReceipt ≡ 4
tauLeptonGen3OverlapRecordsP2Ratio =
  refl

tauLeptonGen3OverlapNoSMPromotion :
  exactStandardModelPromotion canonicalTauLeptonGen3OverlapReceipt
  ≡
  false
tauLeptonGen3OverlapNoSMPromotion =
  refl

tauLeptonGen3OverlapNoPromotion :
  TauLeptonGen3OverlapPromotion →
  ⊥
tauLeptonGen3OverlapNoPromotion =
  tauLeptonGen3OverlapPromotionImpossibleHere
