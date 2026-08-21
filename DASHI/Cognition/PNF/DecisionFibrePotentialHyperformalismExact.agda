module DASHI.Cognition.PNF.DecisionFibrePotentialHyperformalismExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; proj₁)

import DASHI.Cognition.PNF.DecisionPotentialFibreExact as Potential
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Dynamics
import DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact as Order
import DASHI.Cognition.PNF.ActiveInferenceFibreBoundaryExact as FreeEnergy
import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Cognition.PNF.DecisionOutcomeLearningFeedbackExact as Feedback
import DASHI.Cognition.PNF.AttentionValueActuationSeparationExact as Attention
import DASHI.Cognition.PNF.DynamicDecisionFieldCompetitionExact as DFT
import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Cognition.PNF.PNFFastAccessMemoryLearningBridgeExact as AccessPNF
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Reasoning.AttractorAlignedBranchSelectionExact as Branch
import DASHI.Reasoning.AccessBiasFallacySeparationExact as Bias
import DASHI.Reasoning.FallacyObstructionCatalogue as Fallacy
import DASHI.Biology.NeuralDecisionProducerBridgeExact as Neural
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Unified decision-fibre formalism.
--
-- fine state
--   -> momentary accessibility
--   -> live consideration fibre / candidate-generation bias
--   -> formal fallacy/audit layer
--   -> potential + interaction + evidence-accumulation dynamics
--   -> commitment
--   -> actuation gate
--   -> outcome
--   -> learning / future accessibility and transition weight.
--
-- No coordinate is definitionally promoted to another.  Specific theories
-- (DFT, attentional DDM, recurrent attractor networks, quantum-like order
-- effects, active inference) enter as producers/comparison structures over
-- this spine rather than competing foundational ontologies.
------------------------------------------------------------------------

record DecisionFibrePotentialHyperformalism : Set₁ where
  constructor decisionFibrePotentialHyperformalism
  field
    potentialBoundary : Potential.DecisionPotentialBoundary
    operatorSeparation : Dynamics.DecisionOperatorSeparation
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
    Dynamics.canonicalDecisionOperatorSeparation
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

------------------------------------------------------------------------
-- Cross-lane theorem surface.  These are the load-bearing non-collapse laws.
------------------------------------------------------------------------

sameFibreCanCarryDifferentPotential :
  Potential.project Potential.threatState ≡ Potential.project Potential.safetyState
  × Potential.slowPotential Potential.ordinaryContext Potential.threatState ≡ 2
  × Potential.slowPotential Potential.ordinaryContext Potential.safetyState ≡ 0
sameFibreCanCarryDifferentPotential = Potential.sameFibreDifferentPotential

accessFailureIsNotFormalNoTypedMeet :
  ((s : AccessPNF.AccessFormalState) →
    AccessPNF.accessSurface s ≡ false →
    AccessPNF.formalResidual s ≡ Residual.noTypedMeet) → ⊥
accessFailureIsNotFormalNoTypedMeet = AccessPNF.accessFailureCannotForceNoTypedMeet

considerationCanChangePreferenceWithoutChangingStorage :
  Dynamics.preferredCandidate Dynamics.narrowConsideration
  ≡ Dynamics.preferredCandidate Dynamics.broadConsideration → ⊥
considerationCanChangePreferenceWithoutChangingStorage =
  Dynamics.considerationSetCanChangePreferredCandidate

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

commitmentCanFailToActuate :
  Dynamics.commit Dynamics.counterLead ≡ Dynamics.counterCommitted
  × Dynamics.actuate Dynamics.blocked Dynamics.counterCommitted ≡ Dynamics.noAction
commitmentCanFailToActuate = Dynamics.commitmentCanExistWithoutActuation

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
