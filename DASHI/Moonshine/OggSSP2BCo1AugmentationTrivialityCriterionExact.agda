module DASHI.Moonshine.OggSSP2BCo1AugmentationTrivialityCriterionExact where

------------------------------------------------------------------------
-- CO1 AUGMENTATION-FILTRATION TRIVIALITY CRITERION
--
-- Let P ~= F2^24 be the normal elementary-abelian subgroup in 2^24.Co1.
-- For any F2[P.Co1]-module M, the augmentation filtration J^i M has P-trivial
-- graded pieces and multiplication induces Co1-equivariant maps
--
--   (J/J^2) tensor gr_i(M) -> gr_{i+1}(M),
--
-- with J/J^2 ~= the natural 24-dimensional Co1 module.
--
-- Runtime status after the post-Brauer / CTBlocks tranche:
--   * the actual Tate Co1 Jordan-Hoelder profile 1,274,1 is paid;
--   * all four relevant Co1 Hom spaces vanish;
--   * therefore the augmentation criterion is applicable to the actual Tate
--     head.
--
-- What is NOT yet promoted is the generic finite-length extraction lemma:
-- if the normal P action is nontrivial, choose the first nonzero augmentation
-- layer and extract from it a nonzero Co1-equivariant arrow
--
--   24 tensor X -> Y,   X,Y in {1,274}.
--
-- `OggSSP2BAugmentationArrowEliminationExact` already eliminates every such
-- arrow once it is produced.  Thus this extraction lemma is the single
-- remaining proof-theoretic seam on the augmentation route; no runtime premise
-- is missing anymore.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record Co1AugmentationHomReceipt : Set where
  constructor co1-augmentation-hom-receipt
  field
    hom24To1Dimension : Nat
    hom24To274Dimension : Nat
    hom24Tensor274To1Dimension : Nat
    hom24Tensor274To274Dimension : Nat
    allRelevantHomSpacesZero : Bool

record ActualTateCo1ProfileReceipt : Set where
  constructor actual-tate-co1-profile-receipt
  field
    trivialFactorCount : Nat
    factor274Count : Nat
    unidentifiedFactorCount : Nat
    profileIsOne274One : Bool

record Normal2Pow24TrivialityPromotion : Set where
  constructor normal-2pow24-triviality-promotion
  field
    homReceiptRuntimePaid : Bool
    actualTateCo1ProfilePaid : Bool
    augmentationFiltrationCriterionApplicable : Bool
    firstNonzeroLayerExtractionFormalized : Bool
    normal2Pow24ActionOnActualTateProvedTrivial : Bool

canonicalPromotionBoundary : Normal2Pow24TrivialityPromotion
canonicalPromotionBoundary =
  normal-2pow24-triviality-promotion
    true true true false false

homReceiptRuntimeIsPaid :
  Normal2Pow24TrivialityPromotion.homReceiptRuntimePaid
    canonicalPromotionBoundary
  ≡ true
homReceiptRuntimeIsPaid = refl

actualTateCo1ProfileIsPaid :
  Normal2Pow24TrivialityPromotion.actualTateCo1ProfilePaid
    canonicalPromotionBoundary
  ≡ true
actualTateCo1ProfileIsPaid = refl

augmentationCriterionIsApplicable :
  Normal2Pow24TrivialityPromotion.augmentationFiltrationCriterionApplicable
    canonicalPromotionBoundary
  ≡ true
augmentationCriterionIsApplicable = refl

firstNonzeroLayerExtractionStillOpen :
  Normal2Pow24TrivialityPromotion.firstNonzeroLayerExtractionFormalized
    canonicalPromotionBoundary
  ≡ false
firstNonzeroLayerExtractionStillOpen = refl

normal2Pow24TrivialityStillOpen :
  Normal2Pow24TrivialityPromotion.normal2Pow24ActionOnActualTateProvedTrivial
    canonicalPromotionBoundary
  ≡ false
normal2Pow24TrivialityStillOpen = refl

record CriterionStatus : Set where
  constructor criterion-status
  field
    arrowEliminationFormalized : Bool
    firstNonzeroLayerExtractionFormalized : Bool
    gapHomScreenImplemented : Bool
    co1Wedge276ProfileScreenImplemented : Bool
    centralizerBrauerProfileScreenImplemented : Bool
    runtimePremisesPaid : Bool
    actualPromotionPaid : Bool

canonicalCriterionStatus : CriterionStatus
canonicalCriterionStatus =
  criterion-status true false true true true true false
