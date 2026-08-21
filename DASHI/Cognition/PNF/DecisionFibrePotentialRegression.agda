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
import DASHI.Cognition.PNF.FiniteExpectedDecisionPotentialExact as Expected
import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Cognition.PNF.DecisionOutcomeLearningFeedbackExact as Feedback
import DASHI.Cognition.PNF.AttentionValueActuationSeparationExact as Attention
import DASHI.Cognition.PNF.DynamicDecisionFieldCompetitionExact as DFT
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Bounded
import DASHI.Cognition.PNF.GoNoGoActuationGateExact as GoNoGo
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as ActionNF
import DASHI.Cognition.PNF.DecisionStateBundleExact as Bundle
import DASHI.Cognition.PNF.DecisionStateBundleDynamicsExact as BundleDynamics
import DASHI.Cognition.PNF.DecisionActionFibreMultiplicityExact as ActionFibre
import DASHI.Cognition.PNF.ContextualDecisionSubspaceExact as Subspace
import DASHI.Cognition.PNF.ConsiderationSetSelectionExact as Consideration
import DASHI.Cognition.PNF.DecisionPotentialSourceRegistry as Sources
import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Biology.NeuralDecisionProducerBridgeExact as Neural

record DecisionFibrePotentialRegression : Set₁ where
  field
    unified : Unified.DecisionFibrePotentialHyperformalism
    finiteExpectedPotentialBoundary : Expected.FiniteExpectedPotentialBoundary
    bundleBoundary : Bundle.DecisionStateBundleBoundary
    bundleDynamicsBoundary : BundleDynamics.DecisionStateBundleDynamicsBoundary

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
      Potential.slowPotential Potential.blockedSafetyContext Potential.safetyState ≡ 0
      × Potential.slowPotential Potential.blockedSafetyContext Potential.threatState ≡ 2
      × Potential.accessible Potential.blockedSafetyContext Potential.safetyState ≡ false
      × Potential.accessible Potential.blockedSafetyContext Potential.threatState ≡ true

    contextCanHideRepresentedDimension :
      Subspace.bothDimensionsRepresented Subspace.baseState
      ≡ Subspace.bothDimensionsRepresented Subspace.counterPerturbedState
      × Subspace.choiceReadout Subspace.readSupport Subspace.baseState
        ≡ Subspace.choiceReadout Subspace.readSupport Subspace.counterPerturbedState
      × (Subspace.counterSignal Subspace.baseState
          ≡ Subspace.counterSignal Subspace.counterPerturbedState → ⊥)

    observerMinimaConflict :
      FreeEnergy.minimumPolicy FreeEnergy.person
      ≡ FreeEnergy.minimumPolicy FreeEnergy.institution → ⊥

    considerationChangesPreference :
      Dynamics.preferredCandidate Dynamics.narrowConsideration
      ≡ Dynamics.preferredCandidate Dynamics.broadConsideration → ⊥

    localAndFullCarrierOptimaDiffer :
      Consideration.selectedByValue Dynamics.narrowConsideration
      ≡ Consideration.selectedByValue Dynamics.broadConsideration → ⊥

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

    fullBundleActionCannotRecoverCommitment :
      (m : Memory.MemoryFibre) →
      NF.FactorsThrough Bundle.observedAction Bundle.commitmentState → ⊥

    multidimensionalActionFibre :
      (m : Memory.MemoryFibre) → ActionFibre.ActionFibreMultiplicity m

    fullBundleHistoryOrderMatters :
      (m : Memory.MemoryFibre) →
      BundleDynamics.historyABBundle m ≡ BundleDynamics.historyBABundle m → ⊥

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

    sourceCount : Sources.canonicalDecisionSourceCount ≡ 26

open DecisionFibrePotentialRegression public

canonicalDecisionFibrePotentialRegression : DecisionFibrePotentialRegression
canonicalDecisionFibrePotentialRegression = record
  { unified = Unified.canonicalDecisionFibrePotentialHyperformalism
  ; finiteExpectedPotentialBoundary = Expected.canonicalFiniteExpectedPotentialBoundary
  ; bundleBoundary = Bundle.canonicalDecisionStateBundleBoundary
  ; bundleDynamicsBoundary = BundleDynamics.canonicalDecisionStateBundleDynamicsBoundary
  ; sameFibreDifferentPotential = Potential.sameFibreDifferentPotential
  ; bistableFibreComplexity = Potential.bistableFibreHasTwoMinimaAndBarrier
  ; lowerPotentialCanRemainInaccessible = Potential.lowerPotentialNeedNotBeAccessible
  ; contextCanHideRepresentedDimension =
      Subspace.irrelevantDimensionCanRemainRepresentedButChoiceOrthogonal
  ; observerMinimaConflict = FreeEnergy.observerIndexedMinimaDiffer
  ; considerationChangesPreference = Dynamics.considerationSetCanChangePreferredCandidate
  ; localAndFullCarrierOptimaDiffer = Consideration.localAndFullCarrierOptimaCanDiffer
  ; boundedAccumulationSeparatesDeliberationCommitment =
      Bounded.oneRelevantPulseNotYetCommitted , Bounded.twoRelevantPulsesCommit
  ; commitmentNeedNotActuate = Dynamics.sameCommitmentDifferentActuation
  ; goNoGoChangesReleaseForSameCommitment = GoNoGo.sameCommitmentDifferentGoNoGoOutcome
  ; observedActionCannotRecoverFineDecision = ActionNF.actionCannotRecoverFineDecisionState
  ; fullBundleActionCannotRecoverCommitment = Bundle.actionCannotRecoverCommitmentFromBundle
  ; multidimensionalActionFibre = ActionFibre.canonicalActionFibreMultiplicity
  ; fullBundleHistoryOrderMatters = BundleDynamics.bundleHistoryUpdatesDoNotCommute
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
