{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityOSLorentzianF2SpecializationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.YMOSWightmanReconstructionAuthority as OSW

------------------------------------------------------------------------
-- AG-S3 / OS-WIGHTMAN AUTHORITY SPECIALIZED TO THE SELECTED F^2 OPERATOR
--
-- The repository already imports OS/Wightman reconstruction as scoped external
-- authority.  That authority does not identify a particular Euclidean local
-- operator with a particular Minkowski operator.  The only S3-specific physical
-- payment is therefore the operator-level continuation correspondence below.
------------------------------------------------------------------------

record SelectedF2OSLorentzianSpecialization
    (EuclideanOperator LorentzianOperator : Set) : Set₁ where
  field
    reconstruction :
      OSW.OSWightmanReconstructionTheorem

    selectedEuclideanF2 : EuclideanOperator
    selectedLorentzianF2 : LorentzianOperator

    SameAnalyticallyContinuedOperator :
      EuclideanOperator → LorentzianOperator → Set

    selectedF2SameAnalyticallyContinuedOperator :
      SameAnalyticallyContinuedOperator
        selectedEuclideanF2
        selectedLorentzianF2

open SelectedF2OSLorentzianSpecialization public

osWightmanReconstructionAuthorityAlreadyOwned : Bool
osWightmanReconstructionAuthorityAlreadyOwned = true

selectedF2OperatorContinuationStillRequired : Bool
selectedF2OperatorContinuationStillRequired = true

newWightmanReconstructionProofRequiredForS3 : Bool
newWightmanReconstructionProofRequiredForS3 = false

osWightmanReconstructionAuthorityAlreadyOwnedIsTrue :
  osWightmanReconstructionAuthorityAlreadyOwned ≡ true
osWightmanReconstructionAuthorityAlreadyOwnedIsTrue = refl

selectedF2OperatorContinuationStillRequiredIsTrue :
  selectedF2OperatorContinuationStillRequired ≡ true
selectedF2OperatorContinuationStillRequiredIsTrue = refl

newWightmanReconstructionProofRequiredForS3IsFalse :
  newWightmanReconstructionProofRequiredForS3 ≡ false
newWightmanReconstructionProofRequiredForS3IsFalse = refl
