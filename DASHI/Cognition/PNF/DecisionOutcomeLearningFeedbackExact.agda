module DASHI.Cognition.PNF.DecisionOutcomeLearningFeedbackExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning

------------------------------------------------------------------------
-- Decision outcome -> learning -> future access/weight.
--
-- Existing MemoryFibre / LearningAlgebra remain authoritative.  This module
-- only exposes the feedback seam needed by the unified decision formalism.
------------------------------------------------------------------------

data Outcome : Set where
  reinforcingOutcome extinguishingOutcome neutralOutcome : Outcome

learnFromOutcome : Outcome → Memory.MemoryFibre → Memory.MemoryFibre
learnFromOutcome reinforcingOutcome m = Memory.reinforce m
learnFromOutcome extinguishingOutcome m = Memory.extinguishActionDominance m
learnFromOutcome neutralOutcome m = m

futureActionWeight : Outcome → Memory.MemoryFibre → Nat
futureActionWeight outcome m = Memory.actionWeight (learnFromOutcome outcome m)

reinforcementIncreasesFutureWeight :
  (m : Memory.MemoryFibre) →
  futureActionWeight reinforcingOutcome m ≡ suc (Memory.actionWeight m)
reinforcementIncreasesFutureWeight m = refl

extinctionSetsFutureWeightZero :
  (m : Memory.MemoryFibre) →
  futureActionWeight extinguishingOutcome m ≡ zero
extinctionSetsFutureWeightZero m = refl

outcomeLearningPreservesRememberedEvent :
  (outcome : Outcome) →
  (m : Memory.MemoryFibre) →
  Memory.rememberedEvent (learnFromOutcome outcome m)
  ≡ Memory.rememberedEvent m
outcomeLearningPreservesRememberedEvent reinforcingOutcome m = refl
outcomeLearningPreservesRememberedEvent extinguishingOutcome m = refl
outcomeLearningPreservesRememberedEvent neutralOutcome m = refl

------------------------------------------------------------------------
-- Learning receipts are reused, not reconstructed.
------------------------------------------------------------------------

learningReceiptFor : Outcome → Memory.MemoryFibre → Learning.LearningReceipt
learningReceiptFor reinforcingOutcome m = Learning.reinforcementReceipt m
learningReceiptFor extinguishingOutcome m = Learning.extinctionReceipt m
learningReceiptFor neutralOutcome m = Learning.habituationReceipt m

record DecisionLearningBoundary : Set where
  constructor decisionLearningBoundary
  field
    outcomeErasesMemory : Bool
    rewardSignalEqualsCurrentValue : Bool
    learningEqualsDecision : Bool
    futureWeightCanChangeWithContentRetained : Bool

canonicalDecisionLearningBoundary : DecisionLearningBoundary
canonicalDecisionLearningBoundary =
  decisionLearningBoundary false false false true
