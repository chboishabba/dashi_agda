module DASHI.Cognition.PNF.DecisionFibrePotentialRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)

import DASHI.Cognition.PNF.DecisionFibrePotentialHyperformalismExact as Unified
import DASHI.Cognition.PNF.DecisionPotentialFibreExact as Potential
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Dynamics
import DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact as Order
import DASHI.Cognition.PNF.ActiveInferenceFibreBoundaryExact as FreeEnergy
import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Cognition.PNF.DecisionOutcomeLearningFeedbackExact as Feedback
import DASHI.Cognition.PNF.AttentionValueActuationSeparationExact as Attention
import DASHI.Cognition.PNF.DynamicDecisionFieldCompetitionExact as DFT
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Bounded
import DASHI.Cognition.PNF.GoNoGoActuationGateExact as GoNoGo
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as ActionNF
import DASHI.Cognition.PNF.DecisionPotentialSourceRegistry as Sources
import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Biology.NeuralDecisionProducerBridgeExact as Neural

record DecisionFibrePotentialRegression : Set₁ where
  field
    unified : Unified.DecisionFibrePotentialHyperformalism

    sameFibreDifferentPotential :
      Potential.project Potential.threatState ≡ Potential.project Potential.safetyState
      × Potential.slowPotential Potential.ordinaryContext Potential.threatState ≡ 2
      × Potential.slowPotential Potential.ordinaryContext Potential.safetyState ≡ 0

    bistableFibreComplexity :
      Potential.isLocalMinimum Potential.ambivalentContext Potential.threatState ≡ true
      × Potential.isLocalMinimum Potential.ambivalentContext Potential.safetyState ≡ true
      × Potential.localMinimumCount Potential.ambivalentContext ≡ 2
      × Potential.barrierHeight Potential.threatState Potential.safetyState ≡ 3

    lowerPotentialCanRemainInaccessible :
      Potential.slowPotential Potential.threatContext Potential.safetyState ≡ 2
      × Potential.accessible Potential.threatContext Potential.safetyState ≡ false

    observerMinimaConflict :
      FreeEnergy.minimumPolicy FreeEnergy.person
      ≡ FreeEnergy.minimumPolicy FreeEnergy.institution → ⊥

    considerationChangesPreference :
      Dynamics.preferredCandidate Dynamics.narrowConsideration
      ≡ Dynamics.preferredCandidate Dynamics.broadConsideration → ⊥

    boundedAccumulationSeparatesDeliberationCommitment :
      Bounded.threshold (Bounded.contextGate Bounded.attendEvidence Bounded.e0)
      ≡ Bounded.stillDeliberating
      × Bounded.threshold
          (Bounded.contextGate Bounded.attendEvidence
            (Bounded.contextGate Bounded.attendEvidence Bounded.e0))
        ≡ Bounded.committed

    commitmentNeedNotActuate :
      Dynamics.actuate Dynamics.blocked Dynamics.counterCommitted
      ≡ Dynamics.actuate Dynamics.released Dynamics.counterCommitted → ⊥

    goNoGoChangesReleaseForSameCommitment :
      Dynamics.actuate (GoNoGo.releaseGate GoNoGo.high GoNoGo.low)
        Dynamics.supportCommitted
      ≡ Dynamics.actuate (GoNoGo.releaseGate GoNoGo.high GoNoGo.high)
        Dynamics.supportCommitted
      → ⊥

    observedActionCannotRecoverFineDecision :
      NF.FactorsThrough ActionNF.observedAction ActionNF.fineDecisionState → ⊥

    observableCommutationAllowsUpdateNoncommutation :
      Order.observeAThenB Order.initial ≡ Order.observeBThenA Order.initial
      × (Order.AB ≡ Order.BA → ⊥)

    qqViolationRejectsProjectiveDiagnostic :
      Order.QQSatisfied Order.violatingCounts → ⊥

    sameActionDifferentAutonomy :
      Autonomy.emitted Autonomy.autonomousWithdrawal
      ≡ Autonomy.emitted Autonomy.constrainedWithdrawal

    feedbackPreservesRememberedEvent :
      (m : Memory.MemoryFibre) →
      Memory.rememberedEvent
        (Feedback.learnFromOutcome Feedback.reinforcingOutcome m)
      ≡ Memory.rememberedEvent m

    sameValueDifferentAttention :
      Attention.attendedEvidence Attention.attended Pre.counterCandidate
      ≡ Attention.attendedEvidence Attention.unattended Pre.counterCandidate
      → ⊥

    dynamicPreferenceReversal : DFT.earlyState ≡ DFT.laterState → ⊥

    neuralContextChangesCommitment :
      Dynamics.commit (Neural.recurrentStep Neural.supportContext Dynamics.balanced)
      ≡ Dynamics.commit (Neural.recurrentStep Neural.counterContext Dynamics.balanced)
      → ⊥

    balancedConflictRetainsTension :
      Potential.signedSumCancels Potential.positive Potential.negative ≡ true
      × Potential.tensionMass Potential.positive Potential.negative ≡ 2

    sourceCount : Sources.canonicalDecisionSourceCount ≡ 15

open DecisionFibrePotentialRegression public

canonicalDecisionFibrePotentialRegression : DecisionFibrePotentialRegression
canonicalDecisionFibrePotentialRegression = record
  { unified = Unified.canonicalDecisionFibrePotentialHyperformalism
  ; sameFibreDifferentPotential = Potential.sameFibreDifferentPotential
  ; bistableFibreComplexity = Potential.bistableFibreHasTwoMinimaAndBarrier
  ; lowerPotentialCanRemainInaccessible = refl , refl
  ; observerMinimaConflict = FreeEnergy.observerIndexedMinimaDiffer
  ; considerationChangesPreference = Dynamics.considerationSetCanChangePreferredCandidate
  ; boundedAccumulationSeparatesDeliberationCommitment =
      Bounded.oneRelevantPulseNotYetCommitted , Bounded.twoRelevantPulsesCommit
  ; commitmentNeedNotActuate = Dynamics.sameCommitmentDifferentActuation
  ; goNoGoChangesReleaseForSameCommitment = GoNoGo.sameCommitmentDifferentGoNoGoOutcome
  ; observedActionCannotRecoverFineDecision = ActionNF.actionCannotRecoverFineDecisionState
  ; observableCommutationAllowsUpdateNoncommutation =
      Order.observableCommutationDoesNotForceUpdateCommutation
  ; qqViolationRejectsProjectiveDiagnostic = Order.qqNotUniversal
  ; sameActionDifferentAutonomy =
      proj₁ Autonomy.sameActionDoesNotDetermineAutonomy
  ; feedbackPreservesRememberedEvent =
      Feedback.outcomeLearningPreservesRememberedEvent Feedback.reinforcingOutcome
  ; sameValueDifferentAttention = Attention.attentionAndValueAreDistinctAxes
  ; dynamicPreferenceReversal = DFT.preferenceCanReverseOverTrajectory
  ; neuralContextChangesCommitment = Neural.contextCanChangeCommitment
  ; balancedConflictRetainsTension = refl , refl
  ; sourceCount = refl
  }
