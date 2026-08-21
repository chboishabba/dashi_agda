module DASHI.Cognition.PNF.DecisionStateBundleExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Cognition.PNF.AttentionValueActuationSeparationExact as Attention
import DASHI.Cognition.PNF.DecisionPotentialFibreExact as Potential
import DASHI.Cognition.PNF.DynamicDecisionFieldCompetitionExact as DFT
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact as Order
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Dynamics
import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- EXPLICIT DECISION-STATE BUNDLE
--
-- This is the common carrier suggested by the converging decision literatures:
--
--   D_t = (F_o, A_t, C_t, V_t, K_t, H_t, Phi_t, M_t, G_t, L_t)
--
-- Rather than storing redundant derived values, the record retains the fine
-- coordinates from which those surfaces are computed.  The important point is
-- type separation: access is not value; value is not preference; preference is
-- not commitment; commitment is not actuation; action is not the fine state.
------------------------------------------------------------------------

record DecisionStateBundle : Set where
  constructor decisionStateBundle
  field
    fineState : Potential.FineState
    potentialContext : Potential.Context
    accessMode : Pre.AccessMode
    considerationMode : Dynamics.ConsiderationMode
    candidate : Pre.Candidate
    auditStatus : Pre.AuditStatus
    attention : Attention.Attention
    preferenceState : DFT.PreferenceState
    pairInteraction : DFT.Interaction
    historyState : Order.BeliefState
    commitmentState : Dynamics.Commitment
    actuationGate : Dynamics.ActuationGate
    learningState : Memory.MemoryFibre

open DecisionStateBundle public

fibreObservation : DecisionStateBundle → Potential.CoarseObservation
fibreObservation d = Potential.project (fineState d)

accessSurface : DecisionStateBundle → Bool
accessSurface d = Pre.accessible (accessMode d) (candidate d)

considerationSurface : DecisionStateBundle → Bool
considerationSurface d = Dynamics.considered (considerationMode d) (candidate d)

storedValue : DecisionStateBundle → Nat
storedValue d = Attention.storedValue (candidate d)

currentInfluence : DecisionStateBundle → Nat
currentInfluence d = Attention.attendedEvidence (attention d) (candidate d)

potentialSurface : DecisionStateBundle → Nat
potentialSurface d = Potential.slowPotential (potentialContext d) (fineState d)

formalAuditSurface : DecisionStateBundle → Bool
formalAuditSurface d = Pre.auditPasses (auditStatus d)

observedAction : DecisionStateBundle → Dynamics.ExecutedAction
observedAction d = Dynamics.actuate (actuationGate d) (commitmentState d)

historyTrace : DecisionStateBundle → Bool
historyTrace d = Order.trace (historyState d)

learningWeight : DecisionStateBundle → Nat
learningWeight d = Memory.actionWeight (learningState d)

------------------------------------------------------------------------
-- Same retained/fibre/value surface, different live influence.
------------------------------------------------------------------------

attendedBundle : Memory.MemoryFibre → DecisionStateBundle
attendedBundle memory = decisionStateBundle
  Potential.safetyState
  Potential.ordinaryContext
  Pre.broadenedAccess
  Dynamics.broadConsideration
  Pre.counterCandidate
  Pre.cleanAudit
  Attention.attended
  DFT.counterAhead
  DFT.interfering
  Order.initial
  Dynamics.counterCommitted
  Dynamics.released
  memory

unattendedBundle : Memory.MemoryFibre → DecisionStateBundle
unattendedBundle memory = decisionStateBundle
  Potential.safetyState
  Potential.ordinaryContext
  Pre.broadenedAccess
  Dynamics.broadConsideration
  Pre.counterCandidate
  Pre.cleanAudit
  Attention.unattended
  DFT.counterAhead
  DFT.interfering
  Order.initial
  Dynamics.counterCommitted
  Dynamics.released
  memory

sameFineValueDifferentInfluence : (memory : Memory.MemoryFibre) →
  fibreObservation (attendedBundle memory)
    ≡ fibreObservation (unattendedBundle memory)
  × storedValue (attendedBundle memory)
    ≡ storedValue (unattendedBundle memory)
  × (currentInfluence (attendedBundle memory)
      ≡ currentInfluence (unattendedBundle memory) → ⊥)
sameFineValueDifferentInfluence memory = refl , (refl , (λ ()))

------------------------------------------------------------------------
-- Observed action is a lossy projection of the complete decision state.
-- A committed-but-blocked episode and a genuinely uncommitted episode both
-- emit noAction, while their commitment states are provably distinct.
------------------------------------------------------------------------

blockedCommittedBundle : Memory.MemoryFibre → DecisionStateBundle
blockedCommittedBundle memory = decisionStateBundle
  Potential.safetyState
  Potential.ordinaryContext
  Pre.broadenedAccess
  Dynamics.broadConsideration
  Pre.supportingCandidate
  Pre.cleanAudit
  Attention.attended
  DFT.supportAhead
  DFT.interfering
  Order.initial
  Dynamics.supportCommitted
  Dynamics.blocked
  memory

uncommittedBundle : Memory.MemoryFibre → DecisionStateBundle
uncommittedBundle memory = decisionStateBundle
  Potential.safetyState
  Potential.ordinaryContext
  Pre.broadenedAccess
  Dynamics.broadConsideration
  Pre.supportingCandidate
  Pre.cleanAudit
  Attention.attended
  DFT.balanced
  DFT.interfering
  Order.initial
  Dynamics.uncommitted
  Dynamics.released
  memory

sameObservedAction : (memory : Memory.MemoryFibre) →
  observedAction (blockedCommittedBundle memory)
  ≡ observedAction (uncommittedBundle memory)
sameObservedAction memory = refl

commitmentStatesDiffer : (memory : Memory.MemoryFibre) →
  commitmentState (blockedCommittedBundle memory)
  ≡ commitmentState (uncommittedBundle memory) → ⊥
commitmentStatesDiffer memory ()

bundleActionNonFactorabilityWitness : (memory : Memory.MemoryFibre) →
  NF.NonFactorabilityWitness observedAction commitmentState
bundleActionNonFactorabilityWitness memory =
  NF.nonFactorabilityWitness
    (blockedCommittedBundle memory)
    (uncommittedBundle memory)
    (sameObservedAction memory)
    (commitmentStatesDiffer memory)

actionCannotRecoverCommitmentFromBundle : (memory : Memory.MemoryFibre) →
  NF.FactorsThrough observedAction commitmentState → ⊥
actionCannotRecoverCommitmentFromBundle memory =
  NF.witnessRulesOutEveryFlatFactorisation
    (bundleActionNonFactorabilityWitness memory)

bundlesThemselvesDiffer : (memory : Memory.MemoryFibre) →
  blockedCommittedBundle memory ≡ uncommittedBundle memory → ⊥
bundlesThemselvesDiffer memory eq =
  commitmentStatesDiffer memory (cong commitmentState eq)

------------------------------------------------------------------------
-- Boundary: this bundle is a typed carrier for decision-state geometry, not a
-- claim that every biological or social decision instantiates every coordinate
-- in this particular finite witness.
------------------------------------------------------------------------

record DecisionStateBundleBoundary : Set where
  constructor decisionStateBundleBoundary
  field
    actionDeterminesFineDecisionState : Bool
    accessEqualsValue : Bool
    valueEqualsCommitment : Bool
    commitmentEqualsActuation : Bool
    potentialEqualsSemanticIdentity : Bool
    historyCanBeDiscardedWithoutLoss : Bool

canonicalDecisionStateBundleBoundary : DecisionStateBundleBoundary
canonicalDecisionStateBundleBoundary =
  decisionStateBundleBoundary false false false false false false
