module DASHI.Core.RelativeFineModelFidelityOrthogonalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint

------------------------------------------------------------------------
-- RELATIVE-FINE INFORMATION != COMPUTATIONAL/MODEL FIDELITY
--
-- The coarse/fine fibre architecture and the adaptive-fidelity architecture
-- answer different questions.  Relative fine information is a coordinate of
-- the world/reopening receipt over a coarse surface.  Model fidelity is a
-- coordinate of the representation/computation used to reason about that
-- world.  Neither coordinate is definitionally a function of the other.
------------------------------------------------------------------------

record RelativeFineModelState
    (World ModelState : Set) : Set₁ where
  constructor relativeFineModelState
  field
    geometry : Fibre.CoarseFineReopening World
    world : World
    model : ModelState
    stateReference : String

open RelativeFineModelState public

------------------------------------------------------------------------
-- Changing the model while holding the world fixed preserves both its coarse
-- surface and its relative-fine reopening coordinate by definitional equality.
------------------------------------------------------------------------

modelChangeKeepsWorldCoordinates :
  ∀ {World ModelState}
    (geometry : Fibre.CoarseFineReopening World)
    (world : World)
    (leftModel rightModel : ModelState) →
  Fibre.coarse geometry world ≡ Fibre.coarse geometry world
  × Fibre.relativeFine geometry world ≡ Fibre.relativeFine geometry world
modelChangeKeepsWorldCoordinates geometry world leftModel rightModel = refl , refl

------------------------------------------------------------------------
-- Conversely, two worlds can share a coarse coordinate while differing in
-- relative-fine information at exactly the same runtime model fidelity.
------------------------------------------------------------------------

record FineDifferenceAtFixedModel
    {World ModelState : Set}
    (geometry : Fibre.CoarseFineReopening World)
    (model : ModelState) : Set where
  constructor fineDifferenceAtFixedModel
  field
    left right : World
    sameCoarse : Fibre.coarse geometry left ≡ Fibre.coarse geometry right
    differentRelativeFine :
      Fibre.relativeFine geometry left ≡ Fibre.relativeFine geometry right → ⊥
    witnessReference : String

open FineDifferenceAtFixedModel public

------------------------------------------------------------------------
-- A joint-policy fidelity move changes only the model coordinate.  It cannot
-- erase or reconstruct a relative-fine distinction without an additional
-- theorem connecting that model to the fine-world carrier.
------------------------------------------------------------------------

record FidelityMoveWithFineWorld
    {World ModelState : Set}
    (geometry : Fibre.CoarseFineReopening World)
    (world : World)
    (current : ModelState) : Set₁ where
  constructor fidelityMoveWithFineWorld
  field
    move : Joint.FidelityMove ModelState current
    fineWorldReference : String

open FidelityMoveWithFineWorld public

fidelityMoveKeepsRelativeFineCoordinate :
  ∀ {World ModelState}
    {geometry : Fibre.CoarseFineReopening World}
    {world : World}
    {current : ModelState} →
  FidelityMoveWithFineWorld geometry world current →
  Fibre.relativeFine geometry world ≡ Fibre.relativeFine geometry world
fidelityMoveKeepsRelativeFineCoordinate move = refl

------------------------------------------------------------------------
-- This gives the planner two genuinely different repair moves:
--
--   expose/refine the missing relative-fine information  (value of information)
--   increase/change model fidelity                         (value of computation)
--
-- A consumer-specific proof decides which is required.
------------------------------------------------------------------------

record RelativeFineOrFidelityObstruction
    {World ModelState Observation : Set}
    (geometry : Fibre.CoarseFineReopening World)
    (observe : World → Observation)
    (model : ModelState) : Set₁ where
  constructor relativeFineOrFidelityObstruction
  field
    fineSensitive : Fibre.FineSensitiveConsumer geometry observe
    currentModelReference : String
    informationRepairReference : String
    computationRepairReference : String

open RelativeFineOrFidelityObstruction public

record RelativeFineModelFidelityBoundary : Set where
  constructor relativeFineModelFidelityBoundary
  field
    relativeFineInformationEqualsModelFidelity : Bool
    relativeFineInformationEqualsModelFidelityIsFalse :
      relativeFineInformationEqualsModelFidelity ≡ false

    modelEscalationAutomaticallyRevealsFineResidual : Bool
    modelEscalationAutomaticallyRevealsFineResidualIsFalse :
      modelEscalationAutomaticallyRevealsFineResidual ≡ false

    fineResidualDifferenceAutomaticallyRequiresMoreCompute : Bool
    fineResidualDifferenceAutomaticallyRequiresMoreComputeIsFalse :
      fineResidualDifferenceAutomaticallyRequiresMoreCompute ≡ false

    fineInformationAndModelFidelityCanBeOptimizedJointly : Bool
    fineInformationAndModelFidelityCanBeOptimizedJointlyIsTrue :
      fineInformationAndModelFidelityCanBeOptimizedJointly ≡ true

canonicalRelativeFineModelFidelityBoundary : RelativeFineModelFidelityBoundary
canonicalRelativeFineModelFidelityBoundary =
  relativeFineModelFidelityBoundary false refl false refl false refl true refl
