module DASHI.Biology.ObserverRelativeReachableSubfabricExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

------------------------------------------------------------------------
-- OBSERVER/BODY-RELATIVE REACHABLE SUBFABRICS
--
-- world, perceived, accessible and actionable are independent observer layers.
-- This finite witness instantiates one nested case; it does not assert that a
-- universal inclusion theorem holds for every domain without explicit maps.
------------------------------------------------------------------------

data ReachLayer : Set where
  worldLayer perceivedLayer accessibleLayer actionableLayer : ReachLayer

data BodyContext : Set where
  regulatedContext mobilisedContext : BodyContext

data FutureBranch : Set where
  flexiblePlanning seekSupport defensiveWithdrawal : FutureBranch

live : ReachLayer → BodyContext → FutureBranch → Bool

live worldLayer regulatedContext _ = true
live worldLayer mobilisedContext _ = true

live perceivedLayer regulatedContext _ = true
live perceivedLayer mobilisedContext flexiblePlanning = true
live perceivedLayer mobilisedContext seekSupport = true
live perceivedLayer mobilisedContext defensiveWithdrawal = true

live accessibleLayer regulatedContext _ = true
live accessibleLayer mobilisedContext flexiblePlanning = false
live accessibleLayer mobilisedContext seekSupport = false
live accessibleLayer mobilisedContext defensiveWithdrawal = true

live actionableLayer regulatedContext flexiblePlanning = true
live actionableLayer regulatedContext seekSupport = true
live actionableLayer regulatedContext defensiveWithdrawal = true
live actionableLayer mobilisedContext flexiblePlanning = false
live actionableLayer mobilisedContext seekSupport = false
live actionableLayer mobilisedContext defensiveWithdrawal = true

sameWorldDifferentBody :
  (branch : FutureBranch) →
  live worldLayer regulatedContext branch
  ≡ live worldLayer mobilisedContext branch
sameWorldDifferentBody flexiblePlanning = refl
sameWorldDifferentBody seekSupport = refl
sameWorldDifferentBody defensiveWithdrawal = refl

sameWorldButBodyChangesAccessiblePlanning :
  live accessibleLayer regulatedContext flexiblePlanning
  ≡ live accessibleLayer mobilisedContext flexiblePlanning → ⊥
sameWorldButBodyChangesAccessiblePlanning ()

sameWorldButBodyChangesAccessibleSupport :
  live accessibleLayer regulatedContext seekSupport
  ≡ live accessibleLayer mobilisedContext seekSupport → ⊥
sameWorldButBodyChangesAccessibleSupport ()

data AccessibleSupervoxel : Set where
  broadAccessible contractedAccessible reopenedAccessible : AccessibleSupervoxel

liveFibreCount : AccessibleSupervoxel → Nat
liveFibreCount broadAccessible = 3
liveFibreCount contractedAccessible = 1
liveFibreCount reopenedAccessible = 2

broadAndContractedDiffer :
  liveFibreCount broadAccessible ≡ liveFibreCount contractedAccessible → ⊥
broadAndContractedDiffer ()

contractedAndReopenedDiffer :
  liveFibreCount contractedAccessible ≡ liveFibreCount reopenedAccessible → ⊥
contractedAndReopenedDiffer ()

supervoxelCubie : AccessibleSupervoxel → Hyper.AxisBlock 3
supervoxelCubie broadAccessible =
  Hyper.block-cons Hyper.axis-high
    (Hyper.block-cons Hyper.axis-high
      (Hyper.block-cons Hyper.axis-high Hyper.block-root))
supervoxelCubie contractedAccessible =
  Hyper.block-cons Hyper.axis-low
    (Hyper.block-cons Hyper.axis-mid
      (Hyper.block-cons Hyper.axis-low Hyper.block-root))
supervoxelCubie reopenedAccessible =
  Hyper.block-cons Hyper.axis-mid
    (Hyper.block-cons Hyper.axis-high
      (Hyper.block-cons Hyper.axis-mid Hyper.block-root))

record ReachableSubfabricBoundary : Set where
  constructor reachableSubfabricBoundary
  field
    worldPossibilityEqualsAccessibility : Bool
    accessibilityEqualsActionability : Bool
    bodyStateCanGateEffectiveSubfabric : Bool
    canonicalFiniteNestingIsUniversalLaw : Bool
    inaccessibleBranchIsDeletedFromCarrier : Bool

canonicalReachableSubfabricBoundary : ReachableSubfabricBoundary
canonicalReachableSubfabricBoundary =
  reachableSubfabricBoundary false false true false false
