module DASHI.Physics.Closure.VubFromCarrierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Vub from carrier diagnostic receipt.
--
-- The requested naive degree-13 T5 route is recorded as a failure: it gives
-- |Vub| = 0.02467 against the PDG comparison target 0.00369, about 569%
-- high, so no physical Vub or CKM promotion is available.

data VubFromCarrierStatus : Set where
  naiveDegreeThirteenT5VubFailureRecorded :
    VubFromCarrierStatus

data VubFromCarrierBlocker : Set where
  naiveDegreeThirteenT5OvershootsPDG :
    VubFromCarrierBlocker

  missingSuppressionMechanismForVub :
    VubFromCarrierBlocker

  missingPhysicalVubAuthority :
    VubFromCarrierBlocker

canonicalVubFromCarrierBlockers :
  List VubFromCarrierBlocker
canonicalVubFromCarrierBlockers =
  naiveDegreeThirteenT5OvershootsPDG
  ∷ missingSuppressionMechanismForVub
  ∷ missingPhysicalVubAuthority
  ∷ []

data VubFromCarrierPromotion : Set where

vubFromCarrierPromotionImpossibleHere :
  VubFromCarrierPromotion →
  ⊥
vubFromCarrierPromotionImpossibleHere ()

naiveDegreeThirteenT5FormulaLabel : String
naiveDegreeThirteenT5FormulaLabel =
  "naive degree-13 T5 carrier |Vub| diagnostic"

record VubFromCarrierReceipt : Set where
  field
    status :
      VubFromCarrierStatus

    formula :
      String

    formulaIsNaiveDegreeThirteenT5 :
      formula ≡ naiveDegreeThirteenT5FormulaLabel

    carrierDegree :
      Nat

    carrierDegreeIsThirteen :
      carrierDegree ≡ 13

    carrierOperator :
      String

    carrierOperatorIsT5 :
      carrierOperator ≡ "T5"

    naiveVub :
      Float

    pdgVubReference :
      Float

    relativeErrorPercent :
      Float

    relativeErrorLabel :
      String

    naiveT5FailureRecorded :
      Bool

    naiveT5FailureRecordedIsTrue :
      naiveT5FailureRecorded ≡ true

    naiveT5WithinPDGWindow :
      Bool

    naiveT5WithinPDGWindowIsFalse :
      naiveT5WithinPDGWindow ≡ false

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List VubFromCarrierBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVubFromCarrierBlockers

    promotionFlags :
      List VubFromCarrierPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open VubFromCarrierReceipt public

canonicalVubFromCarrierReceipt :
  VubFromCarrierReceipt
canonicalVubFromCarrierReceipt =
  record
    { status =
        naiveDegreeThirteenT5VubFailureRecorded
    ; formula =
        naiveDegreeThirteenT5FormulaLabel
    ; formulaIsNaiveDegreeThirteenT5 =
        refl
    ; carrierDegree =
        13
    ; carrierDegreeIsThirteen =
        refl
    ; carrierOperator =
        "T5"
    ; carrierOperatorIsT5 =
        refl
    ; naiveVub =
        0.02467
    ; pdgVubReference =
        0.00369
    ; relativeErrorPercent =
        569.0
    ; relativeErrorLabel =
        "0.02467 versus PDG 0.00369 is about 569 percent high"
    ; naiveT5FailureRecorded =
        true
    ; naiveT5FailureRecordedIsTrue =
        refl
    ; naiveT5WithinPDGWindow =
        false
    ; naiveT5WithinPDGWindowIsFalse =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalVubFromCarrierBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The naive degree-13 T5 route gives |Vub|=0.02467"
        ∷ "The PDG comparison target recorded here is |Vub|=0.00369"
        ∷ "The resulting overshoot is about 569 percent, so this route is a failure diagnostic"
        ∷ "No physical Vub or CKM promotion is asserted"
        ∷ []
    }

vubFromCarrierDoesNotPromoteCKM :
  physicalCKMPromoted canonicalVubFromCarrierReceipt ≡ false
vubFromCarrierDoesNotPromoteCKM =
  refl
