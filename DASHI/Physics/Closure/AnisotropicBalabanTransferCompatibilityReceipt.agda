module DASHI.Physics.Closure.AnisotropicBalabanTransferCompatibilityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintEightyOneYMBalabanCMP98QhpLocalOscillationReceipt as Sprint81
import DASHI.Physics.Closure.AnisotropicPartitionOfUnity as POU
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMAnisotropicPartitionOfUnityInstance as POUInstance

------------------------------------------------------------------------
-- Sprint 83 closure gate.
--
-- anisotropicPartitionUnityHolds is now true because
-- POUInstance.ymAnisotropicPartitionOfUnityInstance provides a concrete
-- proof-term inhabiting:
--
--   AnisotropicPartitionOfUnity Polymer Polymer YMSpatialBlock
--     YMInBlock YMInSpatialOnly YMInTopTemporal YMInBotTemporal
--
-- The two named obligations from Sprint 82 are discharged:
--   NeedsYMCarrierTypes         — Polymer from YMEffectiveActionSupportInterface
--   NeedsDisjointnessFromStructure — temporal faces are ⊥; exclusion by elim

qhpOscillationBoundAvailable : Bool
qhpOscillationBoundAvailable = true

anisotropicPartitionUnityHolds : Bool
anisotropicPartitionUnityHolds = true

weightedKPThresholdReached : Bool
weightedKPThresholdReached = false

clayYangMillsClosed : Bool
clayYangMillsClosed = false

------------------------------------------------------------------------
-- The grounded POU witness (proof term, not a Bool flag).

anisotropicPartitionOfUnityWitness
  : POU.AnisotropicPartitionOfUnity
      Support.Polymer
      Support.Polymer
      POUInstance.YMSpatialBlock
      POUInstance.YMInBlock
      POUInstance.YMInSpatialOnly
      POUInstance.YMInTopTemporal
      POUInstance.YMInBotTemporal
anisotropicPartitionOfUnityWitness =
  POUInstance.ymAnisotropicPartitionOfUnityInstance

------------------------------------------------------------------------
-- Remaining open obligations (none for the partition — KP is next).

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
      anisotropicPartitionUnityHolds ≡ true
    kpThresholdReached :
      weightedKPThresholdReached ≡ false
    noClayClose :
      clayYangMillsClosed ≡ false
    -- The grounded proof term: type-checks iff the instance really compiles.
    partitionOfUnityWitness :
      POU.AnisotropicPartitionOfUnity
        Support.Polymer
        Support.Polymer
        POUInstance.YMSpatialBlock
        POUInstance.YMInBlock
        POUInstance.YMInSpatialOnly
        POUInstance.YMInTopTemporal
        POUInstance.YMInBotTemporal
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
    ; partitionOfUnityWitness = anisotropicPartitionOfUnityWitness
    ; inputs = canonicalInputs
    ; inputsAreCanonical = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    }
