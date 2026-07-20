module DASHI.Philosophy.MaterialLeverageClosure where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Constructive closure from reflexive orientation to changed feedback.
-- Changed feedback and changed topology remain separate targets.

record LeverageEvidence
       (Reflexive Atlas Organisation Resources Access Safety Time Coordination Operator : Set) : Set₁ where
  field
    reflexive : Reflexive
    atlas : Atlas
    organisation : Organisation
    resources : Resources
    access : Access
    safety : Safety
    time : Time
    coordination : Coordination
    effectiveOperator : Operator

open LeverageEvidence public

record ChangedFeedback (State Operator Outcome : Set) : Set₁ where
  field
    before : State
    operator : Operator
    after : State
    outcome : Outcome
    effectWitness : Set

open ChangedFeedback public

changedFeedbackFromLeverage :
  ∀ {Reflexive Atlas Organisation Resources Access Safety Time Coordination Operator State Outcome : Set} →
  LeverageEvidence Reflexive Atlas Organisation Resources Access Safety Time Coordination Operator →
  State → State → Outcome → Set →
  ChangedFeedback State Operator Outcome
changedFeedbackFromLeverage evidence before after outcome effect =
  record
    { before = before
    ; operator = effectiveOperator evidence
    ; after = after
    ; outcome = outcome
    ; effectWitness = effect
    }

record TopologyPromotionReceipt
       (Feedback TopologyCode : Set) : Set₁ where
  field
    feedback : Feedback
    oldTopology : TopologyCode
    newTopology : TopologyCode
    changedTopologyWitness : Set
    stateChangeAloneSuffices : Bool

open TopologyPromotionReceipt public

record LeverageClosureBoundary : Set where
  constructor mkLeverageClosureBoundary
  field
    reflexivityAloneChangesFeedback : Bool
    completeLeverageCanWitnessFeedback : Bool
    changedFeedbackAutomaticallyChangesTopology : Bool

open LeverageClosureBoundary public

canonicalLeverageClosureBoundary : LeverageClosureBoundary
canonicalLeverageClosureBoundary =
  mkLeverageClosureBoundary false true false

canonicalFeedbackNotAutomaticTopology :
  changedFeedbackAutomaticallyChangesTopology canonicalLeverageClosureBoundary ≡ false
canonicalFeedbackNotAutomaticTopology = refl
