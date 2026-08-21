module DASHI.Cognition.PNF.DecisionFibrePotentialHyperformalismExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; proj₁)

import DASHI.Cognition.PNF.DecisionPotentialFibreExact as Potential
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Dynamics
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Bounded
import DASHI.Cognition.PNF.GoNoGoActuationGateExact as GoNoGo
import DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact as Order
import DASHI.Cognition.PNF.ActiveInferenceFibreBoundaryExact as FreeEnergy
import DASHI.Cognition.PNF.FiniteExpectedDecisionPotentialExact as Expected
import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Cognition.PNF.DecisionOutcomeLearningFeedbackExact as Feedback
import DASHI.Cognition.PNF.AttentionValueActuationSeparationExact as Attention
import DASHI.Cognition.PNF.DynamicDecisionFieldCompetitionExact as DFT
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as ActionNF
import DASHI.Cognition.PNF.DecisionStateBundleExact as Bundle
import DASHI.Cognition.PNF.DecisionStateBundleDynamicsExact as BundleDynamics
import DASHI.Cognition.PNF.DecisionActionFibreMultiplicityExact as ActionFibre
import DASHI.Cognition.PNF.ContextualDecisionSubspaceExact as Subspace
import DASHI.Cognition.PNF.ConsiderationSetSelectionExact as Consideration
import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Cognition.PNF.PNFFastAccessMemoryLearningBridgeExact as AccessPNF
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Reasoning.AttractorAlignedBranchSelectionExact as Branch
import DASHI.Reasoning.AccessBiasFallacySeparationExact as Bias
import DASHI.Reasoning.FallacyObstructionCatalogue as Fallacy
import DASHI.Biology.NeuralDecisionProducerBridgeExact as Neural
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- UNIFIED DECISION-FIBRE / POTENTIAL HYPERFORMALISM
--
-- fine retained state
--   -> momentary accessibility
--   -> live consideration fibre / candidate-generation bias
--   -> formal fallacy/audit layer
--   -> observer/context-indexed potential + interaction + accumulation
--   -> bounded commitment
--   -> Go/NoGo-style actuation gate
--   -> outcome
--   -> learning / future accessibility and transition weight.
--
-- DecisionStateBundleExact makes the snapshot carrier explicit:
--   (F_o, A_t, C_t, V_t, K_t, H_t, Phi_t, M_t, G_t, L_t).
--
-- Specific theories (DFT, attentional DDM, recurrent attractor networks,
-- context-dependent population geometry, bounded accumulation, Go/NoGo
-- gating, quantum-like order effects and active inference) are producers or
-- comparison structures over this spine.  None is promoted to the ontology.
------------------------------------------------------------------------

record DecisionFibrePotentialHyperformalism : Set₁ where
  constructor decisionFibrePotentialHyperformalism
  field
    potentialBoundary : Potential.DecisionPotentialBoundary
    bundleBoundary : Bundle.DecisionStateBundleBoundary
    bundleDynamicsBoundary : BundleDynamics.DecisionStateBundleDynamicsBoundary
    finiteExpectedPotentialBoundary : Expected.FiniteExpectedPotentialBoundary
    contextSubspaceBoundary : Subspace.ContextualDecisionSubspaceBoundary
    considerationSetBoundary : Consideration.ConsiderationSetSelectionBoundary
    operatorSeparation : Dynamics.DecisionOperatorSeparation
    boundedEvidenceBoundary : Bounded.BoundedEvidenceBoundary
    goNoGoBoundary : GoNoGo.GoNoGoBoundary
    quantumLikeBoundary : Order.QuantumLikeDecisionBoundary
    activeInferenceBoundary : FreeEnergy.ActiveInferenceComparisonBoundary
    autonomyBoundary : Autonomy.AutonomyBoundary
    learningBoundary : Feedback.DecisionLearningBoundary
    attentionValueActuationBoundary : Attention.AttentionValueActuationBoundary
    dynamicDecisionFieldBoundary : DFT.DynamicDecisionFieldBoundary
    neuralProducerBoundary : Neural.NeuralDecisionProducerBoundary
    biasFallacyBoundary : Bias.AccessBiasFallacyBoundary
    branchPolicy : Branch.AttractorAlignedPolicy
    preDecisionBoundary : Pre.PreDecisionPipelineBoundary

open DecisionFibrePotentialHyperformalism public

canonicalDecisionFibrePotentialHyperformalism :
  DecisionFibrePotentialHyperformalism
canonicalDecisionFibrePotentialHyperformalism =
  decisionFibrePotentialHyperformalism
    Potential.canonicalDecisionPotentialBoundary
    Bundle.canonicalDecisionStateBundleBoundary
    BundleDynamics.canonicalDecisionStateBundleDynamicsBoundary
    Expected.canonicalFiniteExpectedPotentialBoundary
    Subspace.canonicalContextualDecisionSubspaceBoundary
    Consideration.canonicalConsiderationSetSelectionBoundary
    Dynamics.canonicalDecisionOperatorSeparation
    Bounded.canonicalBoundedEvidenceBoundary
    GoNoGo.canonicalGoNoGoBoundary
    Order.canonicalQuantumLikeDecisionBoundary
    FreeEnergy.canonicalActiveInferenceComparisonBoundary
    Autonomy.canonicalAutonomyBoundary
    Feedback.canonicalDecisionLearningBoundary
    Attention.canonicalAttentionValueActuationBoundary
    DFT.canonicalDynamicDecisionFieldBoundary
    Neural.canonicalNeuralDecisionProducerBoundary
    Bias.canonicalAccessBiasFallacyBoundary
    Branch.canonicalAttractorAlignedPolicy
    Pre.canonicalPreDecisionPipelineBoundary

sameFibreCanCarryDifferentPotential :
  Potential.project Potential.threatState ≡ Potential.project Potential.safetyState
  × Potential.slowPotential Potential.ordinaryContext Potential.threatState ≡ 2
  × Potential.slowPotential Potential.ordinaryContext Potential.safetyState ≡ 0
sameFibreCanCarryDifferentPotential = Potential.sameFibreDifferentPotential

bistableFibreRetainsBarrierComplexity :
  Potential.isLocalMinimum Potential.ambivalentContext Potential.threatState ≡ true
  × Potential.isLocalMinimum Potential.ambivalentContext Potential.safetyState ≡ true
  × Potential.localMinimumCount Potential.ambivalentContext ≡ 2
  × Potential.barrierHeight Potential.threatState Potential.safetyState ≡ 3
bistableFibreRetainsBarrierComplexity = Potential.bistableFibreHasTwoMinimaAndBarrier

accessFailureIsNotFormalNoTypedMeet :
  ((s : AccessPNF.AccessFormalState) →
    AccessPNF.accessSurface s ≡ false →
    AccessPNF.formalResidual s ≡ Residual.noTypedMeet) → ⊥
accessFailureIsNotFormalNoTypedMeet = AccessPNF.accessFailureCannotForceNoTypedMeet

contextualIrrelevanceDoesNotDeleteRepresentation :
  Subspace.bothDimensionsRepresented Subspace.baseState
  ≡ Subspace.bothDimensionsRepresented Subspace.counterPerturbedState
  × Subspace.choiceReadout Subspace.readSupport Subspace.baseState
    ≡ Subspace.choiceReadout Subspace.readSupport Subspace.counterPerturbedState
  × (Subspace.counterSignal Subspace.baseState
      ≡ Subspace.counterSignal Subspace.counterPerturbedState → ⊥)
contextualIrrelevanceDoesNotDeleteRepresentation =
  Subspace.irrelevantDimensionCanRemainRepresentedButChoiceOrthogonal

considerationCanChangePreferenceWithoutChangingStorage :
  Dynamics.preferredCandidate Dynamics.narrowConsideration
  ≡ Dynamics.preferredCandidate Dynamics.broadConsideration → ⊥
considerationCanChangePreferenceWithoutChangingStorage =
  Dynamics.considerationSetCanChangePreferredCandidate

localConsiderationOptimumCanDifferFromFullCarrier :
  Consideration.selectedByValue Dynamics.narrowConsideration
  ≡ Consideration.selectedByValue Dynamics.broadConsideration → ⊥
localConsiderationOptimumCanDifferFromFullCarrier =
  Consideration.localAndFullCarrierOptimaCanDiffer

sameBiasCannotDetermineFormalFallacy :
  (decode : Bias.AccessBias → Fallacy.FallacyObstruction) →
  decode Bias.confirmationAccessBias ≡ Fallacy.missingPremiseSupport →
  decode Bias.confirmationAccessBias ≡ Fallacy.semanticEquivocation →
  ⊥
sameBiasCannotDetermineFormalFallacy = Bias.sameBiasCanFeedDifferentFallacies

sameFallacyCannotDetermineAccessCause :
  (decode : Fallacy.FallacyObstruction → Bias.AccessBias) →
  decode Fallacy.missingPremiseSupport ≡ Bias.threatAccessBias →
  decode Fallacy.missingPremiseSupport ≡ Bias.familiarityAccessBias →
  ⊥
sameFallacyCannotDetermineAccessCause = Bias.sameFallacyCanHaveDifferentAccessCauses

sameStoredValueCanHaveDifferentAttentionEvidence :
  Attention.attendedEvidence Attention.attended Pre.counterCandidate
  ≡ Attention.attendedEvidence Attention.unattended Pre.counterCandidate → ⊥
sameStoredValueCanHaveDifferentAttentionEvidence = Attention.attentionAndValueAreDistinctAxes

preferenceCanReverseAlongDynamicTrajectory : DFT.earlyState ≡ DFT.laterState → ⊥
preferenceCanReverseAlongDynamicTrajectory = DFT.preferenceCanReverseOverTrajectory

boundedAccumulationSeparatesDeliberationAndCommitment :
  Bounded.threshold (Bounded.contextGate Bounded.attendEvidence Bounded.e0)
  ≡ Bounded.stillDeliberating
  × Bounded.threshold
      (Bounded.contextGate Bounded.attendEvidence
        (Bounded.contextGate Bounded.attendEvidence Bounded.e0))
    ≡ Bounded.committed
boundedAccumulationSeparatesDeliberationAndCommitment =
  Bounded.oneRelevantPulseNotYetCommitted , Bounded.twoRelevantPulsesCommit

commitmentCanFailToActuate :
  Dynamics.commit Dynamics.counterLead ≡ Dynamics.counterCommitted
  × Dynamics.actuate Dynamics.blocked Dynamics.counterCommitted ≡ Dynamics.noAction
commitmentCanFailToActuate = Dynamics.commitmentCanExistWithoutActuation

goNoGoCanChangeActuationWithCommitmentFixed :
  Dynamics.actuate (GoNoGo.releaseGate GoNoGo.high GoNoGo.low) Dynamics.supportCommitted
  ≡ Dynamics.actuate (GoNoGo.releaseGate GoNoGo.high GoNoGo.high) Dynamics.supportCommitted
  → ⊥
goNoGoCanChangeActuationWithCommitmentFixed = GoNoGo.sameCommitmentDifferentGoNoGoOutcome

observedActionCannotRecoverFineDecisionState :
  NF.FactorsThrough ActionNF.observedAction ActionNF.fineDecisionState → ⊥
observedActionCannotRecoverFineDecisionState = ActionNF.actionCannotRecoverFineDecisionState

bundleActionCannotRecoverCommitment :
  (memory : Memory.MemoryFibre) →
  NF.FactorsThrough Bundle.observedAction Bundle.commitmentState → ⊥
bundleActionCannotRecoverCommitment = Bundle.actionCannotRecoverCommitmentFromBundle

bundleActionFibreIsMultidimensionallyPlural :
  (memory : Memory.MemoryFibre) → ActionFibre.ActionFibreMultiplicity memory
bundleActionFibreIsMultidimensionallyPlural =
  ActionFibre.canonicalActionFibreMultiplicity

bundleHistoryUpdatesAreNoncommutative :
  (memory : Memory.MemoryFibre) →
  BundleDynamics.historyABBundle memory
  ≡ BundleDynamics.historyBABundle memory → ⊥
bundleHistoryUpdatesAreNoncommutative =
  BundleDynamics.bundleHistoryUpdatesDoNotCommute

observableCommutationDoesNotForceUpdateCommutation :
  Order.observeAThenB Order.initial ≡ Order.observeBThenA Order.initial
  × (Order.AB ≡ Order.BA → ⊥)
observableCommutationDoesNotForceUpdateCommutation =
  Order.observableCommutationDoesNotForceUpdateCommutation

qqIsDiagnosticNotUniversal : Order.QQSatisfied Order.violatingCounts → ⊥
qqIsDiagnosticNotUniversal = Order.qqNotUniversal

observerPotentialMinimaCanConflict :
  FreeEnergy.minimumPolicy FreeEnergy.person
  ≡ FreeEnergy.minimumPolicy FreeEnergy.institution → ⊥
observerPotentialMinimaCanConflict = FreeEnergy.observerIndexedMinimaDiffer

sameActionNeedNotMeanSameAutonomy :
  Autonomy.emitted Autonomy.autonomousWithdrawal
  ≡ Autonomy.emitted Autonomy.constrainedWithdrawal
sameActionNeedNotMeanSameAutonomy =
  proj₁ Autonomy.sameActionDoesNotDetermineAutonomy

outcomeLearningCanChangeFutureWeightWithoutErasure :
  (m : Memory.MemoryFibre) →
  Memory.rememberedEvent
    (Feedback.learnFromOutcome Feedback.reinforcingOutcome m)
  ≡ Memory.rememberedEvent m
outcomeLearningCanChangeFutureWeightWithoutErasure =
  Feedback.outcomeLearningPreservesRememberedEvent Feedback.reinforcingOutcome

neuralContextCanChangeCommitment :
  Dynamics.commit (Neural.recurrentStep Neural.supportContext Dynamics.balanced)
  ≡ Dynamics.commit (Neural.recurrentStep Neural.counterContext Dynamics.balanced) → ⊥
neuralContextCanChangeCommitment = Neural.contextCanChangeCommitment

balancedSignedPressureCanRetainTension :
  Potential.signedSumCancels Potential.positive Potential.negative ≡ true
  × Potential.tensionMass Potential.positive Potential.negative ≡ 2
balancedSignedPressureCanRetainTension = refl , refl
