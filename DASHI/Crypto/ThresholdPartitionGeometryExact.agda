module DASHI.Crypto.ThresholdPartitionGeometryExact where

------------------------------------------------------------------------
-- THRESHOLD / ROUNDING PARTITION GEOMETRY
--
-- A leaked threshold-side bit can be useful without recovering the hidden
-- state.  Multiple independent lossy partitions may jointly identify it.
-- This finite Bool×Bool harness is the exact core; no claim is made that a
-- conforming ML-KEM implementation exposes these predicates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

State : Set
State = Bool × Bool

firstThreshold : State → Bool
firstThreshold = proj₁

secondThreshold : State → Bool
secondThreshold = proj₂

jointThreshold : State → Bool × Bool
jointThreshold state = firstThreshold state , secondThreshold state

-- Each single threshold is lossy.
firstThresholdCollision : firstThreshold (false , false) ≡ firstThreshold (false , true)
firstThresholdCollision = refl

firstCollisionStatesDiffer : (false , false) ≡ (false , true) → ⊥
firstCollisionStatesDiffer ()

secondThresholdCollision : secondThreshold (false , false) ≡ secondThreshold (true , false)
secondThresholdCollision = refl

secondCollisionStatesDiffer : (false , false) ≡ (true , false) → ⊥
secondCollisionStatesDiffer ()

-- Together the two observations are the original state.
twoLossyBitsJointlyRecover : ∀ state → jointThreshold state ≡ state
twoLossyBitsJointlyRecover (false , false) = refl
twoLossyBitsJointlyRecover (false , true) = refl
twoLossyBitsJointlyRecover (true , false) = refl
twoLossyBitsJointlyRecover (true , true) = refl

record ThresholdPartition : Set₁ where
  constructor thresholdPartition
  field
    Hidden Cell : Set
    classify : Hidden → Cell

open ThresholdPartition public

record PartitionCollision (partition : ThresholdPartition) : Set where
  constructor partitionCollision
  field
    left right : Hidden partition
    sameCell : classify partition left ≡ classify partition right
    distinct : left ≡ right → ⊥

open PartitionCollision public

firstPartition : ThresholdPartition
firstPartition = thresholdPartition State Bool firstThreshold

firstPartitionIsLossy : PartitionCollision firstPartition
firstPartitionIsLossy = partitionCollision
  (false , false) (false , true) refl firstCollisionStatesDiffer

-- Distance to a decision boundary and complete-state recovery are therefore
-- separate notions.  This record keeps the distinction proof-relevant.
record BoundarySideObservation : Set₁ where
  constructor boundarySideObservation
  field
    Hidden Side : Set
    side : Hidden → Side

open BoundarySideObservation public
