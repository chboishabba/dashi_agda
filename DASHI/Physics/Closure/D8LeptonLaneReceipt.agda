module DASHI.Physics.Closure.D8LeptonLaneReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- D=-8 lepton-lane candidate.

data D8LeptonLaneStatus : Set where
  d8LeptonLaneCandidateRecorded :
    D8LeptonLaneStatus

data D8LeptonLaneBlocker : Set where
  leptonIdentificationIsCandidate :
    D8LeptonLaneBlocker

  conductorCorrectionRequired :
    D8LeptonLaneBlocker

  chargeAssignmentNotDerived :
    D8LeptonLaneBlocker

canonicalD8LeptonLaneBlockers : List D8LeptonLaneBlocker
canonicalD8LeptonLaneBlockers =
  leptonIdentificationIsCandidate
  ∷ conductorCorrectionRequired
  ∷ chargeAssignmentNotDerived
  ∷ []

data D8LeptonLanePromotion : Set where

d8LeptonLanePromotionImpossibleHere :
  D8LeptonLanePromotion →
  ⊥
d8LeptonLanePromotionImpossibleHere ()

record D8LeptonLaneReceipt : Set where
  field
    status :
      D8LeptonLaneStatus

    discriminant :
      String

    jInvariant :
      Nat

    cmRing :
      String

    conductor :
      Nat

    conductorPreviousMisstatement :
      String

    unitGroup :
      String

    inertPrimeCriterion :
      String

    p3Supersingular :
      Bool

    p3SupersingularIsTrue :
      p3Supersingular ≡ true

    p5Supersingular :
      Bool

    p5SupersingularIsTrue :
      p5Supersingular ≡ true

    pointCountAtP3 :
      Nat

    pointCountAtP5 :
      Nat

    generationOneLeptonLaneCandidate :
      Bool

    generationOneLeptonLaneCandidateIsTrue :
      generationOneLeptonLaneCandidate ≡ true

    leptonLaneDerived :
      Bool

    leptonLaneDerivedIsFalse :
      leptonLaneDerived ≡ false

    leptonSectorPromoted :
      Bool

    leptonSectorPromotedIsFalse :
      leptonSectorPromoted ≡ false

    blockers :
      List D8LeptonLaneBlocker

    blockersAreCanonical :
      blockers ≡ canonicalD8LeptonLaneBlockers

    promotionFlags :
      List D8LeptonLanePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open D8LeptonLaneReceipt public

canonicalD8LeptonLaneReceipt :
  D8LeptonLaneReceipt
canonicalD8LeptonLaneReceipt =
  record
    { status =
        d8LeptonLaneCandidateRecorded
    ; discriminant =
        "D=-8"
    ; jInvariant =
        8000
    ; cmRing =
        "Z[sqrt(-2)]"
    ; conductor =
        8
    ; conductorPreviousMisstatement =
        "Earlier notes sometimes said conductor 4; this receipt records the Hecke-character/discriminant conductor as 8"
    ; unitGroup =
        "Z/2Z"
    ; inertPrimeCriterion =
        "p inert in Q(sqrt(-2)), equivalently p = 3 or 5 mod 8 for odd p"
    ; p3Supersingular =
        true
    ; p3SupersingularIsTrue =
        refl
    ; p5Supersingular =
        true
    ; p5SupersingularIsTrue =
        refl
    ; pointCountAtP3 =
        4
    ; pointCountAtP5 =
        6
    ; generationOneLeptonLaneCandidate =
        true
    ; generationOneLeptonLaneCandidateIsTrue =
        refl
    ; leptonLaneDerived =
        false
    ; leptonLaneDerivedIsFalse =
        refl
    ; leptonSectorPromoted =
        false
    ; leptonSectorPromotedIsFalse =
        refl
    ; blockers =
        canonicalD8LeptonLaneBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "D=-8 is recorded as a generation-1 lepton-lane candidate only"
        ∷ "The conductor is recorded as 8, correcting the earlier conductor-4 shorthand"
        ∷ "No lepton-sector or SM promotion is asserted"
        ∷ []
    }

d8LeptonLaneDoesNotPromoteLeptons :
  leptonSectorPromoted canonicalD8LeptonLaneReceipt ≡ false
d8LeptonLaneDoesNotPromoteLeptons =
  refl

