module DASHI.Physics.Closure.VubAlpha12ProductReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- |V_ub| from the alpha1 * alpha2 up-type Yukawa depth product.
--
-- This receipt records the carrier prediction
--
--   |V_ub| = alpha1 * alpha2 = sqrt(m_u / m_t)
--
-- as a candidate-level leading-order 1-3 Yukawa off-diagonal entry.  The
-- numeric comparison is sqrt(2.16e-3 / 172.7) = 0.003537 against the PDG
-- comparison value 0.003690, an error of about 4.16 percent.

data VubAlpha12ProductStatus : Set where
  vubAlpha12ProductCandidateRecorded :
    VubAlpha12ProductStatus

data VubAlpha12ProductBlocker : Set where
  leadingOrderOnly :
    VubAlpha12ProductBlocker

  missingFullPhysicalCKMDiagonalization :
    VubAlpha12ProductBlocker

  missingPDGAuthorityBindingForExactVub :
    VubAlpha12ProductBlocker

canonicalVubAlpha12ProductBlockers :
  List VubAlpha12ProductBlocker
canonicalVubAlpha12ProductBlockers =
  leadingOrderOnly
  ∷ missingFullPhysicalCKMDiagonalization
  ∷ missingPDGAuthorityBindingForExactVub
  ∷ []

data VubAlpha12ProductPromotion : Set where

vubAlpha12ProductPromotionImpossibleHere :
  VubAlpha12ProductPromotion →
  ⊥
vubAlpha12ProductPromotionImpossibleHere ()

data VubCarrierPredictionFlag : Set where
  candidateAtFourPointSixteenPercent :
    VubCarrierPredictionFlag

vubPredictionFormulaLabel : String
vubPredictionFormulaLabel =
  "|V_ub| = alpha1 * alpha2 = sqrt(m_u/m_t)"

structuralOriginLabel : String
structuralOriginLabel =
  "up-type 1-3 Yukawa depth separation/product of consecutive up-type separations, leading-order 1-3 off-diagonal Yukawa entry"

canonicalVubAlpha12ProductBoundary :
  List String
canonicalVubAlpha12ProductBoundary =
  "The carrier prediction is |V_ub| = alpha1 * alpha2 = sqrt(m_u/m_t)"
  ∷ "Numerically sqrt(2.16e-3 / 172.7) = 0.003537"
  ∷ "The PDG comparison value recorded here is |Vub| = 0.003690"
  ∷ "The relative error is 4.16 percent"
  ∷ "The structural origin is the up-type 1-3 Yukawa depth separation/product of consecutive up-type separations"
  ∷ "The prediction is candidate-level and leading-order only; no physical CKM promotion is asserted"
  ∷ []

record VubAlpha12ProductReceipt : Set where
  field
    status :
      VubAlpha12ProductStatus

    vubPredictionFormula :
      String

    vubPredictionFormulaIsCanonical :
      vubPredictionFormula ≡ vubPredictionFormulaLabel

    vubPredictionValue :
      Float

    vubPredictionValueRecorded :
      vubPredictionValue ≡ 0.003537

    vubPDG :
      Float

    vubPDGRecorded :
      vubPDG ≡ 0.003690

    vubError :
      Float

    vubErrorRecorded :
      vubError ≡ 4.16

    structuralOrigin :
      String

    structuralOriginIsCanonical :
      structuralOrigin ≡ structuralOriginLabel

    leadingOrderThirteenOffDiagonalEntry :
      Bool

    leadingOrderThirteenOffDiagonalEntryIsTrue :
      leadingOrderThirteenOffDiagonalEntry ≡ true

    upTypeDepthProduct :
      Bool

    upTypeDepthProductIsTrue :
      upTypeDepthProduct ≡ true

    vubCarrierPrediction :
      VubCarrierPredictionFlag

    vubCarrierPredictionIsCandidateAtFourPointSixteenPercent :
      vubCarrierPrediction ≡ candidateAtFourPointSixteenPercent

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List VubAlpha12ProductBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVubAlpha12ProductBlockers

    promotionFlags :
      List VubAlpha12ProductPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalVubAlpha12ProductBoundary

open VubAlpha12ProductReceipt public

canonicalVubAlpha12ProductReceipt :
  VubAlpha12ProductReceipt
canonicalVubAlpha12ProductReceipt =
  record
    { status =
        vubAlpha12ProductCandidateRecorded
    ; vubPredictionFormula =
        vubPredictionFormulaLabel
    ; vubPredictionFormulaIsCanonical =
        refl
    ; vubPredictionValue =
        0.003537
    ; vubPredictionValueRecorded =
        refl
    ; vubPDG =
        0.003690
    ; vubPDGRecorded =
        refl
    ; vubError =
        4.16
    ; vubErrorRecorded =
        refl
    ; structuralOrigin =
        structuralOriginLabel
    ; structuralOriginIsCanonical =
        refl
    ; leadingOrderThirteenOffDiagonalEntry =
        true
    ; leadingOrderThirteenOffDiagonalEntryIsTrue =
        refl
    ; upTypeDepthProduct =
        true
    ; upTypeDepthProductIsTrue =
        refl
    ; vubCarrierPrediction =
        candidateAtFourPointSixteenPercent
    ; vubCarrierPredictionIsCandidateAtFourPointSixteenPercent =
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
        canonicalVubAlpha12ProductBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalVubAlpha12ProductBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

vubAlpha12ProductRecordsCandidatePrediction :
  vubCarrierPrediction canonicalVubAlpha12ProductReceipt
  ≡
  candidateAtFourPointSixteenPercent
vubAlpha12ProductRecordsCandidatePrediction =
  refl

vubAlpha12ProductDoesNotPromotePhysicalVub :
  physicalVubPromoted canonicalVubAlpha12ProductReceipt ≡ false
vubAlpha12ProductDoesNotPromotePhysicalVub =
  refl

vubAlpha12ProductDoesNotPromoteCKM :
  physicalCKMPromoted canonicalVubAlpha12ProductReceipt ≡ false
vubAlpha12ProductDoesNotPromoteCKM =
  refl
