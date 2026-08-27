module DASHI.Cognition.PNF.DecisionStateBundleDynamicsExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.DecisionStateBundleExact as Bundle
import DASHI.Cognition.PNF.DecisionPotentialFibreExact as Potential
import DASHI.Cognition.PNF.DynamicDecisionFieldCompetitionExact as DFT
import DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact as Order
import DASHI.Cognition.PNF.DecisionOutcomeLearningFeedbackExact as Feedback
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.AttentionValueActuationSeparationExact as Attention
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Dynamics

------------------------------------------------------------------------
-- COORDINATE-LOCAL DYNAMICS ON THE UNIFIED DECISION BUNDLE
------------------------------------------------------------------------

setAttention : Attention.Attention → Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
setAttention a d = record d { attention = a }

setPotentialContext : Potential.Context → Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
setPotentialContext c d = record d { potentialContext = c }

setPreference : DFT.PreferenceState → Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
setPreference p d = record d { preferenceState = p }

setHistory : Order.BeliefState → Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
setHistory h d = record d { historyState = h }

setCommitment : Dynamics.Commitment → Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
setCommitment c d = record d { commitmentState = c }

setGate : Dynamics.ActuationGate → Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
setGate g d = record d { actuationGate = g }

setLearning : Memory.MemoryFibre → Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
setLearning m d = record d { learningState = m }

applyPreferencePulse : DFT.EvidencePulse → Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
applyPreferencePulse pulse d =
  setPreference (DFT.updatePreference pulse (Bundle.preferenceState d)) d

applyHistoryUpdate :
  (Order.BeliefState → Order.BeliefState) →
  Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
applyHistoryUpdate update d =
  setHistory (update (Bundle.historyState d)) d

applyOutcomeLearning : Feedback.Outcome → Bundle.DecisionStateBundle → Bundle.DecisionStateBundle
applyOutcomeLearning outcome d =
  setLearning (Feedback.learnFromOutcome outcome (Bundle.learningState d)) d

------------------------------------------------------------------------
-- Coordinate changes preserve unrelated projections definitionally.
------------------------------------------------------------------------

attentionChangePreservesFineState :
  (a : Attention.Attention) (d : Bundle.DecisionStateBundle) →
  Bundle.fineState (setAttention a d) ≡ Bundle.fineState d
attentionChangePreservesFineState a d = refl

potentialContextChangePreservesFineState :
  (c : Potential.Context) (d : Bundle.DecisionStateBundle) →
  Bundle.fineState (setPotentialContext c d) ≡ Bundle.fineState d
potentialContextChangePreservesFineState c d = refl

gateChangePreservesCommitment :
  (g : Dynamics.ActuationGate) (d : Bundle.DecisionStateBundle) →
  Bundle.commitmentState (setGate g d) ≡ Bundle.commitmentState d
gateChangePreservesCommitment g d = refl

outcomeLearningPreservesFineDecisionCoordinates :
  (outcome : Feedback.Outcome) (d : Bundle.DecisionStateBundle) →
  Bundle.fineState (applyOutcomeLearning outcome d) ≡ Bundle.fineState d
  × Bundle.commitmentState (applyOutcomeLearning outcome d) ≡ Bundle.commitmentState d
outcomeLearningPreservesFineDecisionCoordinates outcome d = refl , refl

outcomeLearningPreservesRememberedEvent :
  (outcome : Feedback.Outcome) (d : Bundle.DecisionStateBundle) →
  Memory.rememberedEvent (Bundle.learningState (applyOutcomeLearning outcome d))
  ≡ Memory.rememberedEvent (Bundle.learningState d)
outcomeLearningPreservesRememberedEvent outcome d =
  Feedback.outcomeLearningPreservesRememberedEvent outcome (Bundle.learningState d)

------------------------------------------------------------------------
-- The same fine state can move to another potential regime without semantic
-- revision.  On the canonical safety bundle ordinary vs threat context changes
-- potential 0 -> 2 while the coarse fibre observation remains identical.
------------------------------------------------------------------------

contextDeformsPotentialWithoutChangingFibre : (memory : Memory.MemoryFibre) →
  Bundle.fibreObservation
    (setPotentialContext Potential.ordinaryContext (Bundle.attendedBundle memory))
  ≡
  Bundle.fibreObservation
    (setPotentialContext Potential.threatContext (Bundle.attendedBundle memory))
  ×
  (Bundle.potentialSurface
      (setPotentialContext Potential.ordinaryContext (Bundle.attendedBundle memory))
   ≡
   Bundle.potentialSurface
      (setPotentialContext Potential.threatContext (Bundle.attendedBundle memory)) → ⊥)
contextDeformsPotentialWithoutChangingFibre memory = refl , (λ ())

------------------------------------------------------------------------
-- Lift state-update noncommutativity into the full decision bundle.
------------------------------------------------------------------------

historyABBundle : Memory.MemoryFibre → Bundle.DecisionStateBundle
historyABBundle memory =
  applyHistoryUpdate Order.updateB
    (applyHistoryUpdate Order.updateA (Bundle.attendedBundle memory))

historyBABundle : Memory.MemoryFibre → Bundle.DecisionStateBundle
historyBABundle memory =
  applyHistoryUpdate Order.updateA
    (applyHistoryUpdate Order.updateB (Bundle.attendedBundle memory))

historyABProjectsToAB : (memory : Memory.MemoryFibre) →
  Bundle.historyState (historyABBundle memory) ≡ Order.AB
historyABProjectsToAB memory = refl

historyBAProjectsToBA : (memory : Memory.MemoryFibre) →
  Bundle.historyState (historyBABundle memory) ≡ Order.BA
historyBAProjectsToBA memory = refl

bundleHistoryUpdatesDoNotCommute : (memory : Memory.MemoryFibre) →
  historyABBundle memory ≡ historyBABundle memory → ⊥
bundleHistoryUpdatesDoNotCommute memory eq =
  Order.updateMapsDoNotCommute (cong Bundle.historyState eq)

------------------------------------------------------------------------
-- The DFT producer also lifts without rewriting the fine semantic carrier.
------------------------------------------------------------------------

preferencePulsePreservesFineState :
  (pulse : DFT.EvidencePulse) (d : Bundle.DecisionStateBundle) →
  Bundle.fineState (applyPreferencePulse pulse d) ≡ Bundle.fineState d
preferencePulsePreservesFineState pulse d = refl

record DecisionStateBundleDynamicsBoundary : Set where
  constructor decisionStateBundleDynamicsBoundary
  field
    contextPotentialChangeIsSemanticRevision : Bool
    historyOrderCanBeDiscarded : Bool
    outcomeLearningErasesRememberedEvent : Bool
    gateChangeRewritesCommitment : Bool

canonicalDecisionStateBundleDynamicsBoundary : DecisionStateBundleDynamicsBoundary
canonicalDecisionStateBundleDynamicsBoundary =
  decisionStateBundleDynamicsBoundary false false false false
