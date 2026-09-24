{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTTheoryValidationSplitExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- THEORY CONSTRUCTION VS PHYSICAL VALIDATION / PROMOTION
------------------------------------------------------------------------

data GRQFTTheoryCoreLeaf : Set where
  grDiscreteToSmoothEvidence :
    GRQFTTheoryCoreLeaf
  grRecoveryCommutationAndLiteralAttachment :
    GRQFTTheoryCoreLeaf
  qftRecoveryCommutationAndPinnedAttachment :
    GRQFTTheoryCoreLeaf
  cmp119StressLiteralSameObject :
    GRQFTTheoryCoreLeaf
  grToSelectedQFTCrossSectorStressEquality :
    GRQFTTheoryCoreLeaf
  commonOverlapBackreactionAndCorrectionControl :
    GRQFTTheoryCoreLeaf

canonicalGRQFTTheoryCoreLeaves : List GRQFTTheoryCoreLeaf
canonicalGRQFTTheoryCoreLeaves =
  grDiscreteToSmoothEvidence
  ∷ grRecoveryCommutationAndLiteralAttachment
  ∷ qftRecoveryCommutationAndPinnedAttachment
  ∷ cmp119StressLiteralSameObject
  ∷ grToSelectedQFTCrossSectorStressEquality
  ∷ commonOverlapBackreactionAndCorrectionControl
  ∷ []

data GRQFTPhysicalValidationLeaf : Set where
  recoveryPromotionAuthorities :
    GRQFTPhysicalValidationLeaf
  stressWeldAndRegimePromotionAuthorities :
    GRQFTPhysicalValidationLeaf
  acceptedMeasuredGAndUnitCalibration :
    GRQFTPhysicalValidationLeaf
  chosenColliderOrOtherEmpiricalCalibration :
    GRQFTPhysicalValidationLeaf
  novelObservableAgainstEstablishedGRQFT :
    GRQFTPhysicalValidationLeaf
  falsifiableMeasurement :
    GRQFTPhysicalValidationLeaf
  knownLimitValidationIncludingSchwarzschild :
    GRQFTPhysicalValidationLeaf

canonicalGRQFTPhysicalValidationLeaves : List GRQFTPhysicalValidationLeaf
canonicalGRQFTPhysicalValidationLeaves =
  recoveryPromotionAuthorities
  ∷ stressWeldAndRegimePromotionAuthorities
  ∷ acceptedMeasuredGAndUnitCalibration
  ∷ chosenColliderOrOtherEmpiricalCalibration
  ∷ novelObservableAgainstEstablishedGRQFT
  ∷ falsifiableMeasurement
  ∷ knownLimitValidationIncludingSchwarzschild
  ∷ []

w4DrellYanIsPremiseOfMathematicalGRQFTCore : Bool
w4DrellYanIsPremiseOfMathematicalGRQFTCore = false

w4DrellYanIsPremiseOfMathematicalGRQFTCoreIsFalse :
  w4DrellYanIsPremiseOfMathematicalGRQFTCore ≡ false
w4DrellYanIsPremiseOfMathematicalGRQFTCoreIsFalse = refl

commonRegimeBackreactionIsPartOfTheoryCore : Bool
commonRegimeBackreactionIsPartOfTheoryCore = true

commonRegimeBackreactionIsPartOfTheoryCoreIsTrue :
  commonRegimeBackreactionIsPartOfTheoryCore ≡ true
commonRegimeBackreactionIsPartOfTheoryCoreIsTrue = refl

novelObservableIsPartOfTheoryConstructionCore : Bool
novelObservableIsPartOfTheoryConstructionCore = false

novelObservableIsPartOfTheoryConstructionCoreIsFalse :
  novelObservableIsPartOfTheoryConstructionCore ≡ false
novelObservableIsPartOfTheoryConstructionCoreIsFalse = refl
