module DASHI.Physics.Closure.NSCompactGammaFixedFloorScalingObstruction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Fixed positive packet floors cannot cover an amplitude-scaling class.
--
-- This is the kernel form of the small-data warning in the analytic audit.  A
-- finite atlas whose every chart requires the same positive absolute packet
-- floor misses a sufficiently small nonzero rescaling.  Therefore official-data
-- coverage must normalize the packet energy, permit data-dependent floors, or
-- include a direct small/diffuse-data continuation branch.
------------------------------------------------------------------------

record FixedPositivePacketFloorScalingData (i : Level) : Set (lsuc i) where
  field
    State Chart Scale : Set i

    atlas : List Chart
    Occurs : List Chart → Chart → Set i

    baseState : State
    rescale : Scale → State → State
    selectedSmallScale : Scale

    Nonzero : State → Set i
    AdmissibleInChart : Chart → State → Set i
    PacketEnergyAboveFixedFloor : Chart → State → Set i
    PacketEnergyBelowFixedFloor : Chart → State → Set i

    selectedRescalingRemainsNonzero :
      Nonzero (rescale selectedSmallScale baseState)

    admissibleImpliesAboveFixedFloor : ∀ chart state →
      AdmissibleInChart chart state →
      PacketEnergyAboveFixedFloor chart state

    selectedScaleBelowEveryAtlasFloor : ∀ chart →
      Occurs atlas chart →
      PacketEnergyBelowFixedFloor
        chart (rescale selectedSmallScale baseState)

    aboveAndBelowFixedFloorContradict : ∀ chart state →
      PacketEnergyAboveFixedFloor chart state →
      PacketEnergyBelowFixedFloor chart state →
      ⊥

open FixedPositivePacketFloorScalingData public

FiniteAtlasCoversEveryNonzeroState :
  ∀ {i} → FixedPositivePacketFloorScalingData i → Set i
FiniteAtlasCoversEveryNonzeroState D =
  ∀ state → Nonzero D state →
  Σ (Chart D) (λ chart →
    Occurs D (atlas D) chart × AdmissibleInChart D chart state)

fixedPositivePacketFloorFiniteAtlasCannotCoverScalingClass :
  ∀ {i} (D : FixedPositivePacketFloorScalingData i) →
  FiniteAtlasCoversEveryNonzeroState D → ⊥
fixedPositivePacketFloorFiniteAtlasCannotCoverScalingClass D covers
  with covers
    (rescale D (selectedSmallScale D) (baseState D))
    (selectedRescalingRemainsNonzero D)
... | chart , (listed , admissible) =
  aboveAndBelowFixedFloorContradict D
    chart (rescale D (selectedSmallScale D) (baseState D))
    (admissibleImpliesAboveFixedFloor D
      chart (rescale D (selectedSmallScale D) (baseState D)) admissible)
    (selectedScaleBelowEveryAtlasFloor D chart listed)

-- Audit alias.
absoluteQuarterPacketFloorRequiresNormalizationOrDirectBranch :
  ∀ {i} (D : FixedPositivePacketFloorScalingData i) →
  FiniteAtlasCoversEveryNonzeroState D → ⊥
absoluteQuarterPacketFloorRequiresNormalizationOrDirectBranch =
  fixedPositivePacketFloorFiniteAtlasCannotCoverScalingClass
