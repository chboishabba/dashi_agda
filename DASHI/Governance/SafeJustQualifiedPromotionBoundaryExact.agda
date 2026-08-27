module DASHI.Governance.SafeJustQualifiedPromotionBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Governance.SafeJustQualifiedClaimPromotionExact as Promotion

qualifiedPromotionReceipt : Promotion.QualifiedSynthesisPromotion
qualifiedPromotionReceipt = Promotion.canonicalQualifiedSynthesisPromotion

record SafeJustQualifiedPromotionBoundary : Set where
  constructor safeJustQualifiedPromotionBoundary
  field
    qualifiedPromotionIsClosure : Bool
    qualifiedPromotionIsClosureIsFalse : qualifiedPromotionIsClosure ≡ false
    openResidualLedgerSurvivesPromotion : Bool
    openResidualLedgerSurvivesPromotionIsTrue :
      openResidualLedgerSurvivesPromotion ≡ true

canonicalSafeJustQualifiedPromotionBoundary : SafeJustQualifiedPromotionBoundary
canonicalSafeJustQualifiedPromotionBoundary =
  safeJustQualifiedPromotionBoundary false refl true refl
