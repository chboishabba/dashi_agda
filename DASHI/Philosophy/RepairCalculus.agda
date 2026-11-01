module DASHI.Philosophy.RepairCalculus where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Repair is a staged transformation, not restoration of an untouched past.

data RepairStage : Set where
  acknowledgement : RepairStage
  cessationOfHarm : RepairStage
  restitution : RepairStage
  institutionalChange : RepairStage
  trustAssessment : RepairStage
  coexistenceWithoutIntimacy : RepairStage
  irreparableLossRecognition : RepairStage

canonicalRepairStages : List RepairStage
canonicalRepairStages =
  acknowledgement ∷ cessationOfHarm ∷ restitution ∷ institutionalChange ∷
  trustAssessment ∷ coexistenceWithoutIntimacy ∷ irreparableLossRecognition ∷ []

record RepairPath (State Relation Evidence : Set) : Set₁ where
  field
    before : State
    after : State
    relationBefore : Relation
    relationAfter : Relation
    evidence : Evidence
    completedStages : List RepairStage
    harmHasCeased : Set
    seamRemainsVisible : Bool
    returnedToPreviousState : Bool
    restoredTrustRequired : Bool

open RepairPath public

record RepairBoundary : Set where
  constructor mkRepairBoundary
  field
    repairEqualsReturn : Bool
    repairedRelationMustRestoreIntimacy : Bool
    irreparableLossCanRemain : Bool
    institutionalChangeCanBeRequired : Bool
    seamVisibilityCompatibleWithRepair : Bool

open RepairBoundary public

canonicalRepairBoundary : RepairBoundary
canonicalRepairBoundary =
  mkRepairBoundary false false true true true

canonicalRepairIsNotReturn :
  repairEqualsReturn canonicalRepairBoundary ≡ false
canonicalRepairIsNotReturn = refl
