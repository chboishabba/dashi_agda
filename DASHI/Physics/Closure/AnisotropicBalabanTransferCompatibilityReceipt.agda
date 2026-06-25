module DASHI.Physics.Closure.AnisotropicBalabanTransferCompatibilityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintEightyOneYMBalabanCMP98QhpLocalOscillationReceipt as Sprint81
import DASHI.Physics.Closure.AnisotropicPartitionOfUnity as POU

qhpOscillationBoundAvailable : Bool
qhpOscillationBoundAvailable = true

anisotropicPartitionUnityHolds : Bool
anisotropicPartitionUnityHolds = false

weightedKPThresholdReached : Bool
weightedKPThresholdReached = false

clayYangMillsClosed : Bool
clayYangMillsClosed = false

data AnisotropicPartitionUnityObligation : Set where
  NeedsYMCarrierTypes : AnisotropicPartitionUnityObligation
  NeedsDisjointnessFromStructure : AnisotropicPartitionUnityObligation

canonicalObligations : List AnisotropicPartitionUnityObligation
canonicalObligations =
  NeedsYMCarrierTypes
  ∷ NeedsDisjointnessFromStructure
  ∷ []

data AnisotropicBalabanTransferCompatibilityInput : Set where
  QhpOscillationBoundAvailable :
    AnisotropicBalabanTransferCompatibilityInput
  AnisotropicPartitionUnityHolds :
    AnisotropicBalabanTransferCompatibilityInput
  WeightedKPThresholdReached :
    AnisotropicBalabanTransferCompatibilityInput

canonicalInputs : List AnisotropicBalabanTransferCompatibilityInput
canonicalInputs =
  QhpOscillationBoundAvailable
  ∷ AnisotropicPartitionUnityHolds
  ∷ WeightedKPThresholdReached
  ∷ []

data AnisotropicBalabanTransferCompatibilityPromotion : Set where

promotionImpossibleHere :
  AnisotropicBalabanTransferCompatibilityPromotion →
  ⊥
promotionImpossibleHere ()

record AnisotropicBalabanTransferCompatibilityReceipt : Set₁ where
  field
    sprint81OscillationBoundAvailable :
      Sprint81.sprint81ProofAttemptRecorded ≡ true
    oscillationBoundAvailable :
      qhpOscillationBoundAvailable ≡ true
    partitionUnityHolds :
      anisotropicPartitionUnityHolds ≡ false
    kpThresholdReached :
      weightedKPThresholdReached ≡ false
    noClayClose :
      clayYangMillsClosed ≡ false
    missingGroundedCarrierInstance :
      List AnisotropicPartitionUnityObligation
    missingGroundedCarrierInstanceIsCanonical :
      missingGroundedCarrierInstance ≡ canonicalObligations
    inputs :
      List AnisotropicBalabanTransferCompatibilityInput
    inputsAreCanonical :
      inputs ≡ canonicalInputs
    promotions :
      List AnisotropicBalabanTransferCompatibilityPromotion
    promotionsAreEmpty :
      promotions ≡ []

canonicalAnisotropicBalabanTransferCompatibilityReceipt :
  AnisotropicBalabanTransferCompatibilityReceipt
canonicalAnisotropicBalabanTransferCompatibilityReceipt =
  record
    { sprint81OscillationBoundAvailable = refl
    ; oscillationBoundAvailable = refl
    ; partitionUnityHolds = refl
    ; kpThresholdReached = refl
    ; noClayClose = refl
    ; missingGroundedCarrierInstance = canonicalObligations
    ; missingGroundedCarrierInstanceIsCanonical = refl
    ; inputs = canonicalInputs
    ; inputsAreCanonical = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    }


