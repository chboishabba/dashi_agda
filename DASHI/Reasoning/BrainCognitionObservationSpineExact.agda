module DASHI.Reasoning.BrainCognitionObservationSpineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as Decision
import DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient as Brain
import DASHI.Reasoning.AuthorityBooleanPolarityRepairExact as Authority
import DASHI.Reasoning.MaleCNSTypedHyperfabricChartProjectionExact as MaleCNS
import DASHI.Reasoning.FibreRoutingMaleCNSMagnitudeAssignmentReplicationFrontierExact as Replication

------------------------------------------------------------------------
-- BRAIN / COGNITION / OBSERVATION SPINE
--
-- This owner adds no new neuroscience ontology.  It composes existing owners
-- around one common rule:
--
--   latent/fine state -> lossy consumer observation
--
-- and therefore observational equality does not itself authorize latent-state
-- identity or reverse inference.  Memory identity, present influence, decision
-- state, motor policy, connectome structure, imaging readout, and action remain
-- distinct consumers/coordinates unless a separate bridge pays the relation.
------------------------------------------------------------------------

data LatentConsumerQuery : Set where
  rememberedEventQuery : LatentConsumerQuery
  memoryInfluenceQuery : LatentConsumerQuery
  motorPolicyQuery : LatentConsumerQuery
  decisionCommitmentQuery : LatentConsumerQuery
  executedActionQuery : LatentConsumerQuery
  functionalObservationQuery : LatentConsumerQuery

data LatentExtractionStatus : Set where
  candidateOnly : LatentExtractionStatus
  representationAdequacyPaid : LatentExtractionStatus
  decoderIdentityPaid : LatentExtractionStatus

record CandidateLatentConsumerQuestion : Set where
  constructor candidate-latent-consumer-question
  field
    query : LatentConsumerQuery
    fineCarrier : String
    observationSurface : String
    candidateProjection : String
    requiredReceipt : String
    status : LatentExtractionStatus
    interpretation : String

open CandidateLatentConsumerQuestion public

candidateLatentConsumerQuestion : List CandidateLatentConsumerQuestion
candidateLatentConsumerQuestion =
  candidate-latent-consumer-question
    rememberedEventQuery
    "versioned MemoryFibre / remembered PNF event"
    "behavioural, functional-imaging, or other declared observation"
    "consumer-relative quotient of latent state"
    "same-object memory decoder or a non-factorability/adequacy witness for the declared observation"
    candidateOnly
    "Memory identity is represented in the repo, but no MaleCNS/connectome observation currently decodes remembered semantic event identity."
  ∷ candidate-latent-consumer-question
    memoryInfluenceQuery
    "memory valuation/salience/action-weight/retrieval coordinates"
    "declared behaviour or functional observation"
    "consumer-relative influence code"
    "held-out consumer adequacy plus intervention/transport receipt"
    candidateOnly
    "Present influence may change while the remembered event persists; influence is a different consumer from memory identity."
  ∷ candidate-latent-consumer-question
    motorPolicyQuery
    "internal policy / transition / actuation state"
    "executed movement or behavioural action"
    "minimal policy code adequate for a declared future-action consumer"
    "policy-labelled intervention or same-object latent/behaviour binding"
    candidateOnly
    "A compact motor-policy latent is a valid target question, but action alone does not establish its identity."
  ∷ candidate-latent-consumer-question
    decisionCommitmentQuery
    "fine decision state"
    "executed action"
    "action quotient"
    "already-paid non-factorability witness plus any future refined observer"
    representationAdequacyPaid
    "The current repo already proves that identical observed action can hide distinct fine decision states."
  ∷ []

------------------------------------------------------------------------
-- Existing paid theorem anchors.
------------------------------------------------------------------------

memoryContentMayPersistWhileInfluenceChanges :
  ∀ memory →
  Memory.rememberedEvent (Memory.extinguishActionDominance memory)
  ≡ Memory.rememberedEvent memory
memoryContentMayPersistWhileInfluenceChanges =
  Memory.extinctionPreservesRememberedEvent

extinctionLearningPreservesSemanticContent :
  ∀ memory →
  Learning.publicSemanticContentPreserved (Learning.extinctionReceipt memory)
  ≡ true
extinctionLearningPreservesSemanticContent memory =
  Learning.publicSemanticContentPreservedIsTrue (Learning.extinctionReceipt memory)

observedActionDoesNotRecoverFineDecisionState :
  NF.FactorsThrough Decision.observedAction Decision.fineDecisionState → ⊥
observedActionDoesNotRecoverFineDecisionState =
  Decision.actionCannotRecoverFineDecisionState

highResolutionImagingIsObservationChannel :
  Brain.highResolutionFMRIIsObservationChannel
    Brain.canonicalBrainConnectomeFMRIObservationBoundary
  ≡ true
highResolutionImagingIsObservationChannel =
  Brain.highResolutionFMRIIsObservationChannelIsTrue
    Brain.canonicalBrainConnectomeFMRIObservationBoundary

maleCNSHyperfabricProjectionIsExecuted :
  MaleCNS.empiricalHyperfabricRoundtripLosslessForDeclaredConsumer
    MaleCNS.canonicalMaleCNSHyperfabricChartProjectionBoundary
  ≡ true
maleCNSHyperfabricProjectionIsExecuted = refl

maleCNSSenderGainProjectionIsExact :
  MaleCNS.empiricalSenderGainProjectionExact
    MaleCNS.canonicalMaleCNSHyperfabricChartProjectionBoundary
  ≡ true
maleCNSSenderGainProjectionIsExact = refl

maleCNSSenderGainProjectionDoesNotPromoteSufficiency :
  MaleCNS.exactProjectionPromotesSufficiency
    MaleCNS.canonicalMaleCNSHyperfabricChartProjectionBoundary
  ≡ false
maleCNSSenderGainProjectionDoesNotPromoteSufficiency = refl

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data ObservationEqualityImpliesLatentIdentity : Set where

observationEqualityDoesNotAuthorizeLatentIdentity :
  ObservationEqualityImpliesLatentIdentity → ⊥
observationEqualityDoesNotAuthorizeLatentIdentity ()

data ConnectomeDecodesMemoryContent : Set where

connectomeDoesNotDecodeMemoryContent : ConnectomeDecodesMemoryContent → ⊥
connectomeDoesNotDecodeMemoryContent ()

data ConnectomeDecodesMotorPlan : Set where

connectomeDoesNotDecodeMotorPlan : ConnectomeDecodesMotorPlan → ⊥
connectomeDoesNotDecodeMotorPlan ()

data ObservationAuthorizesTraumaInference : Set where

observationDoesNotAuthorizeTraumaInference :
  ObservationAuthorizesTraumaInference → ⊥
observationDoesNotAuthorizeTraumaInference ()

data ConsumerMinimalityImpliesPhysicalLatentDimension : Set where

consumerMinimalityDoesNotIdentifyPhysicalLatentDimension :
  ConsumerMinimalityImpliesPhysicalLatentDimension → ⊥
consumerMinimalityDoesNotIdentifyPhysicalLatentDimension ()

------------------------------------------------------------------------
-- Current bounded state.
------------------------------------------------------------------------

record BrainCognitionObservationSpineBoundary : Set where
  constructor brain-cognition-observation-spine-boundary
  field
    memoryIdentitySeparatedFromCurrentInfluence : Bool
    memoryIdentitySeparatedFromCurrentInfluenceIsTrue :
      memoryIdentitySeparatedFromCurrentInfluence ≡ true

    learningMayChangeInfluenceWithoutSemanticErasure : Bool
    learningMayChangeInfluenceWithoutSemanticErasureIsTrue :
      learningMayChangeInfluenceWithoutSemanticErasure ≡ true

    actionProjectionNonfactorabilityPaid : Bool
    actionProjectionNonfactorabilityPaidIsTrue :
      actionProjectionNonfactorabilityPaid ≡ true

    connectomeConstrainedObservationIsCandidateSurface : Bool
    connectomeConstrainedObservationIsCandidateSurfaceIsTrue :
      connectomeConstrainedObservationIsCandidateSurface ≡ true

    maleCNSStructuralFunctionalProjectionExecuted : Bool
    maleCNSStructuralFunctionalProjectionExecutedIsTrue :
      maleCNSStructuralFunctionalProjectionExecuted ≡ true

    authorityPolarityRepairRequired : Bool
    authorityPolarityRepairRequiredIsTrue :
      authorityPolarityRepairRequired ≡ true

    reverseInferenceBlocked : Bool
    reverseInferenceBlockedIsTrue :
      reverseInferenceBlocked ≡ true

    mindReadingBlocked : Bool
    mindReadingBlockedIsTrue :
      mindReadingBlocked ≡ true

    minimalLearnedLatentExtractionPaid : Bool
    minimalLearnedLatentExtractionPaidIsFalse :
      minimalLearnedLatentExtractionPaid ≡ false

    memoryContentExtractionPaid : Bool
    memoryContentExtractionPaidIsFalse :
      memoryContentExtractionPaid ≡ false

    internalisedMotorPlanExtractionPaid : Bool
    internalisedMotorPlanExtractionPaidIsFalse :
      internalisedMotorPlanExtractionPaid ≡ false

    traumaInferenceFromObservationPaid : Bool
    traumaInferenceFromObservationPaidIsFalse :
      traumaInferenceFromObservationPaid ≡ false

    ninetyPercentUnusedBrainClaimPaid : Bool
    ninetyPercentUnusedBrainClaimPaidIsFalse :
      ninetyPercentUnusedBrainClaimPaid ≡ false

    consumerMinimalRepresentationEqualsPhysicalLatentDimension : Bool
    consumerMinimalRepresentationEqualsPhysicalLatentDimensionIsFalse :
      consumerMinimalRepresentationEqualsPhysicalLatentDimension ≡ false

    replicationIdentityRecoveryEqualsIndependentReplication : Bool
    replicationIdentityRecoveryEqualsIndependentReplicationIsFalse :
      replicationIdentityRecoveryEqualsIndependentReplication ≡ false

    interpretation : String

open BrainCognitionObservationSpineBoundary public

canonicalBrainCognitionObservationSpineBoundary :
  BrainCognitionObservationSpineBoundary
canonicalBrainCognitionObservationSpineBoundary =
  brain-cognition-observation-spine-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Unified bounded thesis: cognitive state is multi-coordinate/history-dependent; memory content may persist while influence changes; learning changes weighting/transition structure; action and imaging are lossy observations; connectome structure constrains candidate dynamics but does not decode memory, motor policy, trauma, or latent identity. MaleCNS pays one structural-to-functional projection result only. Consumer-relative compression may identify a useful minimal representation for a declared task without identifying a physically minimal brain state."

authorityBoundary : Authority.AuthorityBooleanPolarityRepair
authorityBoundary = Authority.canonicalAuthorityBooleanPolarityRepair

replicationFrontier : Replication.MagnitudeReplicationBoundary
replicationFrontier = Replication.canonicalMagnitudeReplicationBoundary
