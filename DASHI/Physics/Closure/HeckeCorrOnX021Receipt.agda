module DASHI.Physics.Closure.HeckeCorrOnX021Receipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Hecke correspondence diagnostic for X_0(21).
--
-- This receipt records a negative diagnostic: X_0(21) is a natural first
-- guess for the p3--p5 lane coupling because lcm(3,7)=21, but the Heegner
-- hypothesis fails for both discriminants used by the two lanes.

data X021HeckeStatus : Set where
  x021HeckeDiagnosticRecorded :
    X021HeckeStatus

data X021HeckeBlocker : Set where
  discriminantMinusThreeRamifiesAtThree :
    X021HeckeBlocker

  discriminantMinusSevenFailsAtLevelTwentyOne :
    X021HeckeBlocker

  heckeCorrespondenceNotDeg23Object :
    X021HeckeBlocker

  deg23RequiresDifferentShimuraSurface :
    X021HeckeBlocker

canonicalX021HeckeBlockers : List X021HeckeBlocker
canonicalX021HeckeBlockers =
  discriminantMinusThreeRamifiesAtThree
  ∷ discriminantMinusSevenFailsAtLevelTwentyOne
  ∷ heckeCorrespondenceNotDeg23Object
  ∷ deg23RequiresDifferentShimuraSurface
  ∷ []

data X021HeckePromotion : Set where

x021HeckePromotionImpossibleHere :
  X021HeckePromotion →
  ⊥
x021HeckePromotionImpossibleHere ()

record HeckeCorrOnX021Receipt : Set where
  field
    status :
      X021HeckeStatus

    modularCurve :
      String

    levelN :
      Nat

    indexMu :
      Nat

    cuspCount :
      Nat

    genusX021 :
      Nat

    genusX021Authority :
      String

    heckePrime :
      Nat

    heckePrimeCoprimeToLevel :
      Bool

    heckePrimeCoprimeToLevelIsTrue :
      heckePrimeCoprimeToLevel ≡ true

    heckeCorrespondenceDegree :
      Nat

    discriminantMinusThreeLocalSymbolAtThree :
      String

    discriminantMinusThreeHeegnerHypothesis :
      Bool

    discriminantMinusThreeHeegnerHypothesisIsFalse :
      discriminantMinusThreeHeegnerHypothesis ≡ false

    discriminantMinusSevenLocalSymbolAtThree :
      String

    discriminantMinusSevenHeegnerHypothesis :
      Bool

    discriminantMinusSevenHeegnerHypothesisIsFalse :
      discriminantMinusSevenHeegnerHypothesis ≡ false

    heegnerHypothesisOnX021FailsForDisc3And7 :
      Bool

    heegnerHypothesisOnX021FailsForDisc3And7IsTrue :
      heegnerHypothesisOnX021FailsForDisc3And7 ≡ true

    heckeCorrOnX021IsDeg23Derivation :
      Bool

    heckeCorrOnX021IsDeg23DerivationIsFalse :
      heckeCorrOnX021IsDeg23Derivation ≡ false

    deg23PhysicalPromoted :
      Bool

    deg23PhysicalPromotedIsFalse :
      deg23PhysicalPromoted ≡ false

    blockers :
      List X021HeckeBlocker

    blockersAreCanonical :
      blockers ≡ canonicalX021HeckeBlockers

    promotionFlags :
      List X021HeckePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open HeckeCorrOnX021Receipt public

canonicalHeckeCorrOnX021Receipt :
  HeckeCorrOnX021Receipt
canonicalHeckeCorrOnX021Receipt =
  record
    { status =
        x021HeckeDiagnosticRecorded
    ; modularCurve =
        "X_0(21)"
    ; levelN =
        21
    ; indexMu =
        32
    ; cuspCount =
        4
    ; genusX021 =
        1
    ; genusX021Authority =
        "standard modular curve table / genus formula for X_0(N)"
    ; heckePrime =
        5
    ; heckePrimeCoprimeToLevel =
        true
    ; heckePrimeCoprimeToLevelIsTrue =
        refl
    ; heckeCorrespondenceDegree =
        6
    ; discriminantMinusThreeLocalSymbolAtThree =
        "(-3/3) = 0, so 3 ramifies rather than splits"
    ; discriminantMinusThreeHeegnerHypothesis =
        false
    ; discriminantMinusThreeHeegnerHypothesisIsFalse =
        refl
    ; discriminantMinusSevenLocalSymbolAtThree =
        "(-7 mod 3) = 2, non-square mod 3"
    ; discriminantMinusSevenHeegnerHypothesis =
        false
    ; discriminantMinusSevenHeegnerHypothesisIsFalse =
        refl
    ; heegnerHypothesisOnX021FailsForDisc3And7 =
        true
    ; heegnerHypothesisOnX021FailsForDisc3And7IsTrue =
        refl
    ; heckeCorrOnX021IsDeg23Derivation =
        false
    ; heckeCorrOnX021IsDeg23DerivationIsFalse =
        refl
    ; deg23PhysicalPromoted =
        false
    ; deg23PhysicalPromotedIsFalse =
        refl
    ; blockers =
        canonicalX021HeckeBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "X_0(21) is genus one, but neither D=-3 nor D=-7 satisfies the Heegner hypothesis at level 21"
        ∷ "T_5 on X_0(21) has correspondence degree 6, not the p3-p5 inter-lane degree"
        ∷ "No deg23 or CKM promotion is asserted here"
        ∷ []
    }

heckeX021DoesNotPromoteDeg23 :
  deg23PhysicalPromoted canonicalHeckeCorrOnX021Receipt ≡ false
heckeX021DoesNotPromoteDeg23 =
  refl

