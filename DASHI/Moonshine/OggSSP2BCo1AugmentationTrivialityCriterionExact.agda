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
-- Therefore, if every composition factor of M|Co1 is in {1,274} and all four
-- relevant Hom spaces vanish
--
--   Hom(24,1), Hom(24,274), Hom(24 tensor 274,1),
--   Hom(24 tensor 274,274),
--
-- then every augmentation multiplication map is zero, hence JM=0 and P acts
-- trivially.  This is the exact theorem shape tested by the GAP Hom screen.
--
-- This Agda owner records the proof interface and fail-closed promotion state;
-- it does NOT replace the runtime Hom calculation or the separate proof that
-- the actual Tate head has Co1 composition profile 1,274,1.
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
    normal2Pow24ActionOnActualTateProvedTrivial : Bool

canonicalPromotionBoundary : Normal2Pow24TrivialityPromotion
canonicalPromotionBoundary =
  normal-2pow24-triviality-promotion
    false false false false

record CriterionStatus : Set where
  constructor criterion-status
  field
    augmentationFiltrationArgumentFormalized : Bool
    gapHomScreenImplemented : Bool
    co1Wedge276ProfileScreenImplemented : Bool
    centralizerBrauerProfileScreenImplemented : Bool
    actualPromotionPaid : Bool

canonicalCriterionStatus : CriterionStatus
canonicalCriterionStatus =
  criterion-status true true true true false
