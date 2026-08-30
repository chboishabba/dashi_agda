module DASHI.Core.RelativeFineModelFidelityOrthogonalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint

------------------------------------------------------------------------
-- RELATIVE-FINE INFORMATION != COMPUTATIONAL/MODEL FIDELITY
--
-- The coarse/fine fibre architecture and adaptive-fidelity architecture answer
-- different questions. Relative fine information is a coordinate of the world
-- or reopening receipt over a coarse surface. Model fidelity is a coordinate of
-- the representation/computation used to reason about that world.
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

modelChangeKeepsWorldCoordinates :
  ∀ {World ModelState}
    (geometry : Fibre.CoarseFineReopening World)
    (world : World)
    (leftModel rightModel : ModelState) →
  Fibre.coarse geometry world ≡ Fibre.coarse geometry world
  × Fibre.relativeFine geometry world ≡ Fibre.relativeFine geometry world
modelChangeKeepsWorldCoordinates geometry world leftModel rightModel = refl , refl

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
-- Relative-fine disclosure is an evidence move, not a fidelity move.  The
-- application still supplies its resource cost and calibration/realisation
-- reference; the generic theorem only says what information is disclosed.
------------------------------------------------------------------------

relativeFineEvidenceMove :
  ∀ {World}
    (geometry : Fibre.CoarseFineReopening World) →
  (measurementCost : Nat) →
  String →
  String →
  Joint.EvidenceMove World
relativeFineEvidenceMove geometry measurementCost resourceRef calibrationRef =
  Joint.evidenceMove
    (Choice.informationMove
      Choice.takeMeasurement
      measurementCost
      "disclose relative-fine reopening coordinate"
      resourceRef
      calibrationRef)
    Joint.measurementEvidence
    (Fibre.RelativeFine geometry)
    (λ world observed → Fibre.relativeFine geometry world ≡ observed)
    "relative-fine fibre observation"
    calibrationRef

relativeFineObservationRefinesWithoutChangingModel :
  ∀ {World ModelState}
    (geometry : Fibre.CoarseFineReopening World)
    (live : World → Set)
    (model : ModelState)
    (measurementCost : Nat)
    (resourceRef calibrationRef : String)
    (observed : Fibre.RelativeFine geometry) →
  Joint.RefineLive
    live
    (relativeFineEvidenceMove geometry measurementCost resourceRef calibrationRef)
    observed
  ≡
  (λ world → live world × Fibre.relativeFine geometry world ≡ observed)
relativeFineObservationRefinesWithoutChangingModel
    geometry live model measurementCost resourceRef calibrationRef observed = refl

------------------------------------------------------------------------
-- The planner therefore has two different repair moves for a coarse collision:
-- reveal/refine the missing relative-fine coordinate (value of information),
-- or increase/change model fidelity (value of computation).
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

    relativeFineCanBeDisclosedAsEvidenceAtFixedModel : Bool
    relativeFineCanBeDisclosedAsEvidenceAtFixedModelIsTrue :
      relativeFineCanBeDisclosedAsEvidenceAtFixedModel ≡ true

    fineInformationAndModelFidelityCanBeOptimizedJointly : Bool
    fineInformationAndModelFidelityCanBeOptimizedJointlyIsTrue :
      fineInformationAndModelFidelityCanBeOptimizedJointly ≡ true

canonicalRelativeFineModelFidelityBoundary : RelativeFineModelFidelityBoundary
canonicalRelativeFineModelFidelityBoundary =
  relativeFineModelFidelityBoundary
    false refl false refl false refl true refl true refl
