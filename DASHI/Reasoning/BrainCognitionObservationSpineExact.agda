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
import DASHI.Reasoning.ConsumerRelativeLatentExtractionExact as Latent
import DASHI.Reasoning.MaleCNSTypedHyperfabricChartProjectionExact as MaleCNS
import DASHI.Reasoning.FibreRoutingMaleCNSMagnitudeAssignmentReplicationFrontierExact as Replication

------------------------------------------------------------------------
-- BRAIN / COGNITION / OBSERVATION SPINE
--
-- This owner adds no new neuroscience ontology. It composes existing owners
-- around one common rule:
--
--   latent/fine state -> lossy consumer observation.
--
-- Exact extraction of a requested latent L from observation Q is a separate
-- factorisation obligation L = decode o Q. Observational equality therefore
-- does not itself authorize latent-state identity or reverse inference.
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
    "FactorsThrough observation rememberedEvent, or a non-factorability witness proving this observer cannot decode it"
    candidateOnly
    "Memory identity is represented in the repo, but no MaleCNS/connectome observation currently decodes remembered semantic event identity."
  ∷ candidate-latent-consumer-question
    memoryInfluenceQuery
    "memory valuation/salience/action-weight/retrieval coordinates"
    "declared behaviour or functional observation"
    "consumer-relative influence code"
    "FactorsThrough observation requested influence coordinate plus held-out/intervention adequacy for the declared consumer"
    candidateOnly
    "Present influence may change while the remembered event persists; influence is a different latent query from memory identity."
  ∷ candidate-latent-consumer-question
    motorPolicyQuery
    "internal policy / transition / actuation state"
    "executed movement or behavioural action"
    "minimal policy code adequate for a declared future-action consumer"
    "FactorsThrough observation motorPolicy with policy-labelled intervention or same-object latent/behaviour binding"
    candidateOnly
    "A compact motor-policy latent is a valid target question, but action alone does not establish its identity."
  ∷ candidate-latent-consumer-question
    decisionCommitmentQuery
    "fine decision state"
    "executed action"
    "action quotient"
    "existing NonFactorabilityWitness already proves this action observer cannot decode the fine state"
    representationAdequacyPaid
    "The current repo proves that identical observed action can hide distinct fine decision states."
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
  Latent.CanExtractLatent Decision.observedAction Decision.fineDecisionState → ⊥
observedActionDoesNotRecoverFineDecisionState =
  Latent.decisionFineStateNotExtractableFromAction

latentExtractionIsFactorisation :
  ∀ {State Observation RequestedLatent : Set}
    (observe : State → Observation)
    (latent : State → RequestedLatent) →
  Set₁
latentExtractionIsFactorisation = Latent.CanExtractLatent

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
-- Current bounded state / missing-fields ledger.
------------------------------------------------------------------------

record BrainLatentExtractionMissingFields : Set where
  constructor brain-latent-extraction-missing-fields
  field
    rememberedEventDecoder : Bool
    memoryInfluenceDecoder : Bool
    internalisedMotorPolicyDecoder : Bool
    fineDecisionStateDecoderFromAction : Bool
    refinedDecisionObserverNeeded : Bool
    sameObjectLatentObservationBindingNeeded : Bool
    interventionOrTransportReceiptNeeded : Bool
    interpretation : String

open BrainLatentExtractionMissingFields public

currentBrainLatentExtractionMissingFields : BrainLatentExtractionMissingFields
currentBrainLatentExtractionMissingFields = brain-latent-extraction-missing-fields
  false
  false
  false
  false
  true
  true
  true
  "Open latent-extraction obligations are query-specific. Action-only fine-decision decoding is ruled out by an existing non-factorability witness; memory identity, memory influence, and motor-policy decoding need their own observation bindings/factorisation receipts rather than inheriting authority from the connectome or MaleCNS compression result."

record BrainCognitionObservationSpineBoundary : Set where
  constructor brain-cognition-observation-spine-boundary
  field
    memoryIdentitySeparatedFromCurrentInfluence : Bool
    memoryIdentitySeparatedFromCurrentInfluenceIsTrue :
      memoryIdentitySeparatedFromCurrentInfluence ≡ true

    learningMayChangeInfluenceWithoutSemanticErasure : Bool
    learningMayChangeInfluenceWithoutSemanticErasureIsTrue :
      learningMayChangeInfluenceWithoutSemanticErasure ≡ true

    exactLatentExtractionRequiresFactorisation : Bool
    exactLatentExtractionRequiresFactorisationIsTrue :
      exactLatentExtractionRequiresFactorisation ≡ true

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
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Unified bounded thesis: cognitive state is multi-coordinate/history-dependent; memory content may persist while influence changes; learning changes weighting/transition structure; action and imaging are lossy observations; exact latent extraction is a consumer-specific factorisation obligation. Connectome structure constrains candidate dynamics but does not decode memory, motor policy, trauma, or latent identity. MaleCNS pays one structural-to-functional projection result only. Consumer-relative compression may identify a useful minimal representation for a declared task without identifying a physically minimal brain state."

authorityBoundary : Authority.AuthorityBooleanPolarityRepair
authorityBoundary = Authority.canonicalAuthorityBooleanPolarityRepair

latentExtractionFrontier : Latent.LatentExtractionFrontier
latentExtractionFrontier = Latent.canonicalLatentExtractionFrontier

replicationFrontier : Replication.MagnitudeReplicationBoundary
replicationFrontier = Replication.canonicalMagnitudeReplicationBoundary
