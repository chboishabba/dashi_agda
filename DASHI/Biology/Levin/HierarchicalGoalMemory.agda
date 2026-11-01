module DASHI.Biology.Levin.HierarchicalGoalMemory where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; _⊔_; lsuc)

------------------------------------------------------------------------
-- Stratified pattern memory.
--
-- This captures the distinction between an expressed target and a deeper
-- target capable of restoring or replacing it.  It is a typed control
-- hierarchy, not a claim that every organism has metacognition.

record HierarchicalGoalSystem {ℓs ℓl ℓg : Level} :
  Set (lsuc (ℓs ⊔ ℓl ⊔ ℓg)) where
  field
    State : Set ℓs
    GoalLevel : Set ℓl
    Goal : Set ℓg

    expressedLevel : State → GoalLevel
    expressedGoal  : State → Goal
    metaLevel      : State → GoalLevel
    metaGoal       : State → Goal

    evolve : State → State
    sameGoal : Goal → Goal → Bool
    levelAbove : GoalLevel → GoalLevel → Bool

open HierarchicalGoalSystem public

record TransientGoalWitness
  {ℓs ℓl ℓg : Level}
  (S : HierarchicalGoalSystem {ℓs} {ℓl} {ℓg}) : Set ℓs where
  field
    initial : State S
    later   : State S
    laterIsOneStep : later ≡ evolve S initial
    expressedDiffersFromMetaInitially :
      sameGoal S (expressedGoal S initial) (metaGoal S initial) ≡ false
    higherControllerPresent :
      levelAbove S (metaLevel S initial) (expressedLevel S initial) ≡ true
    metaGoalRestoredLater :
      sameGoal S (expressedGoal S later) (metaGoal S initial) ≡ true

open TransientGoalWitness public

record PersistentRewriteWitness
  {ℓs ℓl ℓg : Level}
  (S : HierarchicalGoalSystem {ℓs} {ℓl} {ℓg}) : Set ℓs where
  field
    before after : State S
    rewritePersistsOneStep : evolve S after ≡ after
    targetChanged :
      sameGoal S (expressedGoal S before) (expressedGoal S after) ≡ false
    noDeeperRestorationPressure :
      sameGoal S (expressedGoal S after) (metaGoal S after) ≡ true

open PersistentRewriteWitness public

canonicalHierarchicalGoalNotes : List String
canonicalHierarchicalGoalNotes =
  "A transient anatomical target and a persistent rewritten target are distinct witness types"
  ∷ "A deeper goal may restore an expressed goal without implying human-like metacognition"
  ∷ "Persistence is stated relative to an explicit evolution law and observation horizon"
  ∷ "No universal claim about planaria, aging, cancer, or human regeneration is promoted"
  ∷ []

record HierarchicalGoalBoundary : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    hierarchyIsNotMetacognitionByDefinition : Bool
    hierarchyIsNotMetacognitionByDefinitionIsFalse :
      hierarchyIsNotMetacognitionByDefinition ≡ false

    temporaryTargetIsNotPermanentRewrite : Bool
    temporaryTargetIsNotPermanentRewriteIsFalse :
      temporaryTargetIsNotPermanentRewrite ≡ false

open HierarchicalGoalBoundary public

canonicalHierarchicalGoalBoundary : HierarchicalGoalBoundary
canonicalHierarchicalGoalBoundary = record
  { candidateOnly = true
  ; candidateOnlyIsTrue = refl
  ; hierarchyIsNotMetacognitionByDefinition = false
  ; hierarchyIsNotMetacognitionByDefinitionIsFalse = refl
  ; temporaryTargetIsNotPermanentRewrite = false
  ; temporaryTargetIsNotPermanentRewriteIsFalse = refl
  }
