module DASHI.Governance.FeministClimateQualifiedPromotionExact where

open import DASHI.Core.Prelude
import DASHI.Core.MultiaxialResidualBundleExact as Multi
import DASHI.Governance.SafeJustQualifiedClaimPromotionExact as SafePromotion
import DASHI.Governance.FeministClimateJusticeResidualBundleExact as Residual

------------------------------------------------------------------------
-- FEMINIST-CLIMATE QUALIFIED PROMOTION
--
-- Extends #625's proof-carrying synthesis promotion with a typed five-axis
-- residual contract.  The result is usable for the declared research-synthesis
-- consumer while remaining explicitly non-closed politically, distributively,
-- categorically and phenomenally.
------------------------------------------------------------------------

record FeministClimateQualifiedPromotion : Set₁ where
  constructor feministClimateQualifiedPromotion
  field
    safeJustPromotion : SafePromotion.QualifiedSynthesisPromotion
    residualBundle : Residual.ClimateJusticeResidualBundle
    residualCarriage :
      Multi.ResidualCarriageReceipt
        Residual.researchSynthesisResidualContract
        residualBundle

open FeministClimateQualifiedPromotion public

canonicalFeministClimateQualifiedPromotion : FeministClimateQualifiedPromotion
canonicalFeministClimateQualifiedPromotion =
  feministClimateQualifiedPromotion
    SafePromotion.canonicalQualifiedSynthesisPromotion
    Residual.canonicalClimateJusticeResiduals
    Residual.canonicalResidualCarriage

record FeministClimatePromotionBoundary : Set where
  constructor feministClimatePromotionBoundary
  field
    qualifiedPromotionErasesPhenomenonResidual : Bool
    qualifiedPromotionErasesPhenomenonResidualIsFalse :
      qualifiedPromotionErasesPhenomenonResidual ≡ false
    qualifiedPromotionErasesEpistemicResidual : Bool
    qualifiedPromotionErasesEpistemicResidualIsFalse :
      qualifiedPromotionErasesEpistemicResidual ≡ false
    qualifiedPromotionErasesPoliticalResidual : Bool
    qualifiedPromotionErasesPoliticalResidualIsFalse :
      qualifiedPromotionErasesPoliticalResidual ≡ false
    qualifiedPromotionErasesResponsibilityResidual : Bool
    qualifiedPromotionErasesResponsibilityResidualIsFalse :
      qualifiedPromotionErasesResponsibilityResidual ≡ false
    qualifiedPromotionErasesCategoryResidual : Bool
    qualifiedPromotionErasesCategoryResidualIsFalse :
      qualifiedPromotionErasesCategoryResidual ≡ false
    qualifiedPromotionIsSemanticClosure : Bool
    qualifiedPromotionIsSemanticClosureIsFalse :
      qualifiedPromotionIsSemanticClosure ≡ false

canonicalFeministClimatePromotionBoundary : FeministClimatePromotionBoundary
canonicalFeministClimatePromotionBoundary =
  feministClimatePromotionBoundary
    false refl false refl false refl false refl false refl false refl
