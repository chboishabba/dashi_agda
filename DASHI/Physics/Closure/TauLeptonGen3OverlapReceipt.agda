module DASHI.Physics.Closure.TauLeptonGen3OverlapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- D=-12 tau-lane overlap receipt.
--
-- This receipt records the D=-12 tau-lane overlap diagnostics.  The level
-- convention is explicitly ambiguous and both level-6 and level-12 routes
-- are retained.  The ratios are diagnostic overlaps only; no tau, lepton,
-- Yukawa, or Standard Model promotion is asserted here.

data TauLeptonGen3OverlapStatus : Set where
  tauLeptonGen3OverlapDiagnosticRecorded :
    TauLeptonGen3OverlapStatus

data TauLeptonGen3LevelConvention : Set where
  levelSixConvention :
    TauLeptonGen3LevelConvention

  levelTwelveConvention :
    TauLeptonGen3LevelConvention

data TauLeptonGen3OverlapBlocker : Set where
  levelConventionAmbiguous :
    TauLeptonGen3OverlapBlocker

  overlapRatioIsDiagnosticOnly :
    TauLeptonGen3OverlapBlocker

  missingTauYukawaCarrierMap :
    TauLeptonGen3OverlapBlocker

  missingLeptonGenerationPromotionAuthority :
    TauLeptonGen3OverlapBlocker

canonicalTauLeptonGen3OverlapBlockers :
  List TauLeptonGen3OverlapBlocker
canonicalTauLeptonGen3OverlapBlockers =
  levelConventionAmbiguous
  ∷ overlapRatioIsDiagnosticOnly
  ∷ missingTauYukawaCarrierMap
  ∷ missingLeptonGenerationPromotionAuthority
  ∷ []

data TauLeptonGen3OverlapPromotion : Set where

tauLeptonGen3OverlapPromotionImpossibleHere :
  TauLeptonGen3OverlapPromotion →
  ⊥
tauLeptonGen3OverlapPromotionImpossibleHere ()

levelAmbiguityLabel : String
levelAmbiguityLabel =
  "D=-12 tau-lane level is recorded with both level 6 and level 12 conventions"

levelSixOverlapLabel : String
levelSixOverlapLabel =
  "level 6 route: psi(3)=4, vol X0(3)=4*pi/3; psi(6)=12, vol X0(6)=4*pi; ratio to p3/c-s lane = 1/3"

levelTwelveOverlapLabel : String
levelTwelveOverlapLabel =
  "level 12 route: psi(4)=6, vol X0(4)=2*pi; psi(12)=24, vol X0(12)=8*pi; ratio to p2/u-d lane = 1/4"

record TauLeptonGen3OverlapReceipt : Setω where
  field
    status :
      TauLeptonGen3OverlapStatus

    discriminant :
      String

    discriminantIsMinusTwelve :
      discriminant ≡ "D=-12"

    levelAmbiguityStatement :
      String

    levelAmbiguityStatementIsCanonical :
      levelAmbiguityStatement ≡ levelAmbiguityLabel

    levelConventions :
      List TauLeptonGen3LevelConvention

    levelConventionsAreCanonical :
      levelConventions ≡ levelSixConvention ∷ levelTwelveConvention ∷ []

    levelSix :
      Nat

    levelSixIsSix :
      levelSix ≡ 6

    levelTwelve :
      Nat

    levelTwelveIsTwelve :
      levelTwelve ≡ 12

    psi3 :
      Nat

    psi3IsFour :
      psi3 ≡ 4

    volX03Numerator :
      Nat

    volX03NumeratorIsFour :
      volX03Numerator ≡ 4

    volX03Denominator :
      Nat

    volX03DenominatorIsThree :
      volX03Denominator ≡ 3

    psi6 :
      Nat

    psi6IsTwelve :
      psi6 ≡ 12

    volX06Numerator :
      Nat

    volX06NumeratorIsFour :
      volX06Numerator ≡ 4

    volX06Denominator :
      Nat

    volX06DenominatorIsOne :
      volX06Denominator ≡ 1

    ratioToP3CSLaneNumerator :
      Nat

    ratioToP3CSLaneNumeratorIsOne :
      ratioToP3CSLaneNumerator ≡ 1

    ratioToP3CSLaneDenominator :
      Nat

    ratioToP3CSLaneDenominatorIsThree :
      ratioToP3CSLaneDenominator ≡ 3

    gcd63 :
      Nat

    gcd63IsThree :
      gcd63 ≡ 3

    levelSixOverlapStatement :
      String

    levelSixOverlapStatementIsCanonical :
      levelSixOverlapStatement ≡ levelSixOverlapLabel

    psi4 :
      Nat

    psi4IsSix :
      psi4 ≡ 6

    volX04Numerator :
      Nat

    volX04NumeratorIsTwo :
      volX04Numerator ≡ 2

    volX04Denominator :
      Nat

    volX04DenominatorIsOne :
      volX04Denominator ≡ 1

    psi12 :
      Nat

    psi12IsTwentyFour :
      psi12 ≡ 24

    volX012Numerator :
      Nat

    volX012NumeratorIsEight :
      volX012Numerator ≡ 8

    volX012Denominator :
      Nat

    volX012DenominatorIsOne :
      volX012Denominator ≡ 1

    ratioToP2UDLaneNumerator :
      Nat

    ratioToP2UDLaneNumeratorIsOne :
      ratioToP2UDLaneNumerator ≡ 1

    ratioToP2UDLaneDenominator :
      Nat

    ratioToP2UDLaneDenominatorIsFour :
      ratioToP2UDLaneDenominator ≡ 4

    gcd124 :
      Nat

    gcd124IsFour :
      gcd124 ≡ 4

    levelTwelveOverlapStatement :
      String

    levelTwelveOverlapStatementIsCanonical :
      levelTwelveOverlapStatement ≡ levelTwelveOverlapLabel

    tauLaneOverlapDiagnosticRecorded :
      Bool

    tauLaneOverlapDiagnosticRecordedIsTrue :
      tauLaneOverlapDiagnosticRecorded ≡ true

    levelAmbiguityRecorded :
      Bool

    levelAmbiguityRecordedIsTrue :
      levelAmbiguityRecorded ≡ true

    promotedToTauLepton :
      Bool

    promotedToTauLeptonIsFalse :
      promotedToTauLepton ≡ false

    physicalLeptonPromoted :
      Bool

    physicalLeptonPromotedIsFalse :
      physicalLeptonPromoted ≡ false

    physicalYukawaPromoted :
      Bool

    physicalYukawaPromotedIsFalse :
      physicalYukawaPromoted ≡ false

    physicalSMPromoted :
      Bool

    physicalSMPromotedIsFalse :
      physicalSMPromoted ≡ false

    blockers :
      List TauLeptonGen3OverlapBlocker

    blockersAreCanonical :
      blockers ≡ canonicalTauLeptonGen3OverlapBlockers

    promotionFlags :
      List TauLeptonGen3OverlapPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open TauLeptonGen3OverlapReceipt public

canonicalTauLeptonGen3OverlapReceipt :
  TauLeptonGen3OverlapReceipt
canonicalTauLeptonGen3OverlapReceipt =
  record
    { status =
        tauLeptonGen3OverlapDiagnosticRecorded
    ; discriminant =
        "D=-12"
    ; discriminantIsMinusTwelve =
        refl
    ; levelAmbiguityStatement =
        levelAmbiguityLabel
    ; levelAmbiguityStatementIsCanonical =
        refl
    ; levelConventions =
        levelSixConvention ∷ levelTwelveConvention ∷ []
    ; levelConventionsAreCanonical =
        refl
    ; levelSix =
        6
    ; levelSixIsSix =
        refl
    ; levelTwelve =
        12
    ; levelTwelveIsTwelve =
        refl
    ; psi3 =
        4
    ; psi3IsFour =
        refl
    ; volX03Numerator =
        4
    ; volX03NumeratorIsFour =
        refl
    ; volX03Denominator =
        3
    ; volX03DenominatorIsThree =
        refl
    ; psi6 =
        12
    ; psi6IsTwelve =
        refl
    ; volX06Numerator =
        4
    ; volX06NumeratorIsFour =
        refl
    ; volX06Denominator =
        1
    ; volX06DenominatorIsOne =
        refl
    ; ratioToP3CSLaneNumerator =
        1
    ; ratioToP3CSLaneNumeratorIsOne =
        refl
    ; ratioToP3CSLaneDenominator =
        3
    ; ratioToP3CSLaneDenominatorIsThree =
        refl
    ; gcd63 =
        3
    ; gcd63IsThree =
        refl
    ; levelSixOverlapStatement =
        levelSixOverlapLabel
    ; levelSixOverlapStatementIsCanonical =
        refl
    ; psi4 =
        6
    ; psi4IsSix =
        refl
    ; volX04Numerator =
        2
    ; volX04NumeratorIsTwo =
        refl
    ; volX04Denominator =
        1
    ; volX04DenominatorIsOne =
        refl
    ; psi12 =
        24
    ; psi12IsTwentyFour =
        refl
    ; volX012Numerator =
        8
    ; volX012NumeratorIsEight =
        refl
    ; volX012Denominator =
        1
    ; volX012DenominatorIsOne =
        refl
    ; ratioToP2UDLaneNumerator =
        1
    ; ratioToP2UDLaneNumeratorIsOne =
        refl
    ; ratioToP2UDLaneDenominator =
        4
    ; ratioToP2UDLaneDenominatorIsFour =
        refl
    ; gcd124 =
        4
    ; gcd124IsFour =
        refl
    ; levelTwelveOverlapStatement =
        levelTwelveOverlapLabel
    ; levelTwelveOverlapStatementIsCanonical =
        refl
    ; tauLaneOverlapDiagnosticRecorded =
        true
    ; tauLaneOverlapDiagnosticRecordedIsTrue =
        refl
    ; levelAmbiguityRecorded =
        true
    ; levelAmbiguityRecordedIsTrue =
        refl
    ; promotedToTauLepton =
        false
    ; promotedToTauLeptonIsFalse =
        refl
    ; physicalLeptonPromoted =
        false
    ; physicalLeptonPromotedIsFalse =
        refl
    ; physicalYukawaPromoted =
        false
    ; physicalYukawaPromotedIsFalse =
        refl
    ; physicalSMPromoted =
        false
    ; physicalSMPromotedIsFalse =
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
        "D=-12 tau-lane overlap is recorded with both level-6 and level-12 conventions"
        ∷ "Level 6 route gives psi(3)=4, vol X0(3)=4*pi/3, psi(6)=12, vol X0(6)=4*pi, and ratio 1/3 to the p3/c-s lane"
        ∷ "Level 12 route gives psi(4)=6, vol X0(4)=2*pi, psi(12)=24, vol X0(12)=8*pi, and ratio 1/4 to the p2/u-d lane"
        ∷ "The overlaps gcd(6,3)=3 and gcd(12,4)=4 are recorded"
        ∷ "No tau, lepton, Yukawa, or Standard Model promotion is asserted"
        ∷ []
    }

tauLeptonGen3OverlapRecordsLevelAmbiguity :
  levelAmbiguityRecorded canonicalTauLeptonGen3OverlapReceipt ≡ true
tauLeptonGen3OverlapRecordsLevelAmbiguity =
  refl

tauLeptonGen3OverlapRecordsP3Ratio :
  ratioToP3CSLaneDenominator canonicalTauLeptonGen3OverlapReceipt ≡ 3
tauLeptonGen3OverlapRecordsP3Ratio =
  refl

tauLeptonGen3OverlapRecordsP2Ratio :
  ratioToP2UDLaneDenominator canonicalTauLeptonGen3OverlapReceipt ≡ 4
tauLeptonGen3OverlapRecordsP2Ratio =
  refl

tauLeptonGen3OverlapDoesNotPromoteTau :
  promotedToTauLepton canonicalTauLeptonGen3OverlapReceipt ≡ false
tauLeptonGen3OverlapDoesNotPromoteTau =
  refl

tauLeptonGen3OverlapDoesNotPromoteSM :
  physicalSMPromoted canonicalTauLeptonGen3OverlapReceipt ≡ false
tauLeptonGen3OverlapDoesNotPromoteSM =
  refl

tauLeptonGen3OverlapNoPromotion :
  TauLeptonGen3OverlapPromotion →
  ⊥
tauLeptonGen3OverlapNoPromotion =
  tauLeptonGen3OverlapPromotionImpossibleHere
