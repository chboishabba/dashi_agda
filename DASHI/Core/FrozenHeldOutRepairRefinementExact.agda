module DASHI.Core.FrozenHeldOutRepairRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen

------------------------------------------------------------------------
-- FROZEN SELECTION AS A STRICT REFINEMENT OF HELD-OUT REPAIR
--
-- `RobustExperimentInferenceFrontierExact.HeldOutRepair` already separates
-- training fit from held-out prediction.  `FrozenSelectionReceipt` adds a
-- different methodological payment: the selection/refinement rule was fixed
-- before downstream/held-out outcomes were consulted.
--
-- Neither coordinate implies the other, so the reusable object is their
-- conjunction rather than a replacement owner or a mirrored status enum.
------------------------------------------------------------------------

record FrozenHeldOutRepair
    (Rule Repair Training HeldOut Prediction : Set) : Set₁ where
  constructor frozen-heldout-repair
  field
    heldOutRepair : Robust.HeldOutRepair Repair Training HeldOut Prediction
    frozenSelection : Frozen.FrozenSelectionReceipt Rule

open FrozenHeldOutRepair public

retainsHeldOutRepair :
  ∀ {Rule Repair Training HeldOut Prediction : Set} →
  FrozenHeldOutRepair Rule Repair Training HeldOut Prediction →
  Robust.HeldOutRepair Repair Training HeldOut Prediction
retainsHeldOutRepair = heldOutRepair

retainsFrozenSelection :
  ∀ {Rule Repair Training HeldOut Prediction : Set} →
  FrozenHeldOutRepair Rule Repair Training HeldOut Prediction →
  Frozen.FrozenSelectionReceipt Rule
retainsFrozenSelection = frozenSelection

------------------------------------------------------------------------
-- Orthogonality firewalls.
------------------------------------------------------------------------

data HeldOutRepairAutomaticallyFrozen : Set where
data FrozenSelectionAutomaticallyCreatesHeldOutRepair : Set where
data TrainingFitCreatesHeldOutValidity : Set where

heldOutRepairDoesNotAutomaticallyFreezeSelection :
  HeldOutRepairAutomaticallyFrozen → ⊥
heldOutRepairDoesNotAutomaticallyFreezeSelection ()

frozenSelectionDoesNotAutomaticallyCreateHeldOutRepair :
  FrozenSelectionAutomaticallyCreatesHeldOutRepair → ⊥
frozenSelectionDoesNotAutomaticallyCreateHeldOutRepair ()

trainingFitDoesNotCreateHeldOutValidity :
  TrainingFitCreatesHeldOutValidity → ⊥
trainingFitDoesNotCreateHeldOutValidity ()

record FrozenHeldOutRepairBoundary : Set where
  constructor frozen-heldout-repair-boundary
  field
    heldOutRepairParentRetained : Bool
    heldOutRepairParentRetainedIsTrue : heldOutRepairParentRetained ≡ true
    frozenSelectionRetainedSeparately : Bool
    frozenSelectionRetainedSeparatelyIsTrue :
      frozenSelectionRetainedSeparately ≡ true
    heldOutRepairImpliesFrozenSelection : Bool
    heldOutRepairImpliesFrozenSelectionIsFalse :
      heldOutRepairImpliesFrozenSelection ≡ false
    frozenSelectionImpliesHeldOutRepair : Bool
    frozenSelectionImpliesHeldOutRepairIsFalse :
      frozenSelectionImpliesHeldOutRepair ≡ false
    conjunctionCreatesDynamicSafety : Bool
    conjunctionCreatesDynamicSafetyIsFalse :
      conjunctionCreatesDynamicSafety ≡ false
    conjunctionCreatesQueryAdequacy : Bool
    conjunctionCreatesQueryAdequacyIsFalse :
      conjunctionCreatesQueryAdequacy ≡ false

canonicalFrozenHeldOutRepairBoundary : FrozenHeldOutRepairBoundary
canonicalFrozenHeldOutRepairBoundary =
  frozen-heldout-repair-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
