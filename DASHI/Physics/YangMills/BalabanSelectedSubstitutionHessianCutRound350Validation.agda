{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedSubstitutionHessianCutRound350Validation where

------------------------------------------------------------------------
-- RED-first validation root for the R347 boundary-comparison decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSelectedSubstitutionHessianCutRound350Exact as R350

selectedHessianStabilityLevel : ProofLevel
selectedHessianStabilityLevel = R350.selectedHessianStabilityLevel

selectedSubstitutionMarkedLevel : ProofLevel
selectedSubstitutionMarkedLevel = R350.selectedSubstitutionMarkedLevel

genericSubstitutionToCoefficientCompilerLevel : ProofLevel
genericSubstitutionToCoefficientCompilerLevel =
  R350.genericSubstitutionToCoefficientCompilerLevel

freshCauchyCoefficientAnalysisRequired : Bool
freshCauchyCoefficientAnalysisRequired = R350.freshCauchyCoefficientAnalysisRequired

freshCauchyCoefficientAnalysisRequiredIsFalse :
  freshCauchyCoefficientAnalysisRequired ≡ false
freshCauchyCoefficientAnalysisRequiredIsFalse =
  R350.freshCauchyCoefficientAnalysisRequiredIsFalse

selectedCoefficientAttachmentStillIndependent : Bool
selectedCoefficientAttachmentStillIndependent =
  R350.selectedCoefficientAttachmentStillIndependent

selectedCoefficientAttachmentStillIndependentIsTrue :
  selectedCoefficientAttachmentStillIndependent ≡ true
selectedCoefficientAttachmentStillIndependentIsTrue =
  R350.selectedCoefficientAttachmentStillIndependentIsTrue

clayPromotion : Bool
clayPromotion = R350.clayPromotion

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = R350.clayPromotionIsFalse
