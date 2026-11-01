module DASHI.Physics.Closure.EichlerSelbergAtCMPointReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

data LocalT13CMFact : Set where
  thirteenSplitsInDiscMinusThree :
    LocalT13CMFact

  thirteenInertInDiscMinusSeven :
    LocalT13CMFact

  discMinusSevenSupersingularAtThirteen :
    LocalT13CMFact

  localCMEigenvalueVanishes :
    LocalT13CMFact

canonicalLocalT13CMFacts : List LocalT13CMFact
canonicalLocalT13CMFacts =
  thirteenSplitsInDiscMinusThree
  ∷ thirteenInertInDiscMinusSeven
  ∷ discMinusSevenSupersingularAtThirteen
  ∷ localCMEigenvalueVanishes
  ∷ []

record EichlerSelbergAtCMPointReceipt : Setω where
  field
    legendreMinusThreeOverThirteenPlusOne :
      Bool

    legendreMinusThreeOverThirteenPlusOneIsTrue :
      legendreMinusThreeOverThirteenPlusOne ≡ true

    legendreMinusSevenOverThirteenMinusOne :
      Bool

    legendreMinusSevenOverThirteenMinusOneIsTrue :
      legendreMinusSevenOverThirteenMinusOne ≡ true

    a13DiscMinusThree :
      Nat

    a13DiscMinusThreeIsTwo :
      a13DiscMinusThree ≡ 2

    eMinus3F13PointCount :
      Nat

    eMinus3F13PointCountIsTwelve :
      eMinus3F13PointCount ≡ 12

    eJZeroF13PointCount :
      Nat

    eJZeroF13PointCountIsTwelve :
      eJZeroF13PointCount ≡ 12

    a13DiscMinusSeven :
      Nat

    a13DiscMinusSevenIsZero :
      a13DiscMinusSeven ≡ 0

    localCMEigenvalue :
      Nat

    localCMEigenvalueIsZero :
      localCMEigenvalue ≡ 0

    cmCorrectionExplainsDeg23Residual :
      Bool

    cmCorrectionExplainsDeg23ResidualIsFalse :
      cmCorrectionExplainsDeg23Residual ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    facts :
      List LocalT13CMFact

    factsAreCanonical :
      facts ≡ canonicalLocalT13CMFacts

open EichlerSelbergAtCMPointReceipt public

canonicalEichlerSelbergAtCMPointReceipt :
  EichlerSelbergAtCMPointReceipt
canonicalEichlerSelbergAtCMPointReceipt =
  record
    { legendreMinusThreeOverThirteenPlusOne =
        true
    ; legendreMinusThreeOverThirteenPlusOneIsTrue =
        refl
    ; legendreMinusSevenOverThirteenMinusOne =
        true
    ; legendreMinusSevenOverThirteenMinusOneIsTrue =
        refl
    ; a13DiscMinusThree =
        2
    ; a13DiscMinusThreeIsTwo =
        refl
    ; eMinus3F13PointCount =
        12
    ; eMinus3F13PointCountIsTwelve =
        refl
    ; eJZeroF13PointCount =
        12
    ; eJZeroF13PointCountIsTwelve =
        refl
    ; a13DiscMinusSeven =
        0
    ; a13DiscMinusSevenIsZero =
        refl
    ; localCMEigenvalue =
        0
    ; localCMEigenvalueIsZero =
        refl
    ; cmCorrectionExplainsDeg23Residual =
        false
    ; cmCorrectionExplainsDeg23ResidualIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; facts =
        canonicalLocalT13CMFacts
    ; factsAreCanonical =
        refl
    }

eichlerSelbergAtCMPointPhysicalCKMFalse :
  physicalCKMPromoted canonicalEichlerSelbergAtCMPointReceipt ≡ false
eichlerSelbergAtCMPointPhysicalCKMFalse =
  refl
