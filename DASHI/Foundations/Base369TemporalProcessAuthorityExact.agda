module DASHI.Foundations.Base369TemporalProcessAuthorityExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Recordings witness exact proposition nodes rather than generic agreement.
-- Starting a process is separated from authorising every future act; revocation
-- is separated from unavoidable continuation and required closure.  Temporal
-- reconstruction and proposition-corruption records prevent occurrence,
-- distress or inappropriateness from being promoted automatically into intent,
-- systematic pattern or legal character.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

open import DASHI.Foundations.SSPTritCarrier using (SSPTrit)
import DASHI.Foundations.Base369PropositionResponseTransportExact as Response

record RecordingWitness : Set₁ where
  constructor recordingWitness
  field
    Participant : Set
    participant : Participant
    node : Response.PropositionNode
    episode : Response.DecisionEpisode
    responseTime : Nat
    provenance : Response.ProvenanceKind
    exactActionRecovered : Set
    antecedentRecovered : Set
    modalityRecovered : Set
    scopeRecovered : Set
    decisionWindowRecovered : Set
    exceptionsRecovered : Set
    unresolvedConditionsRecovered : Set

open RecordingWitness public

data PostRevocationActKind : Set where
  alreadyCompleted
  unavoidableContinuation
  requiredClosureStep
  newDiscretionaryStep : PostRevocationActKind

record ProcessAuthority : Set₁ where
  constructor processAuthority
  field
    Process Act : Set
    process : Process
    authorisedStart : Act
    revocationTime : Nat
    classifyAfterRevocation : Act → PostRevocationActKind

open ProcessAuthority public

record FreshAuthorityRequired
  (authority : ProcessAuthority)
  (act : Act authority) : Set₁ where
  constructor freshAuthorityRequired
  field
    isNewDiscretionary :
      classifyAfterRevocation authority act ≡ newDiscretionaryStep
    freshWitness : Set

open FreshAuthorityRequired public

record ProcessInertia : Set where
  constructor processInertia
  field
    institutional technical legal practical : Nat

open ProcessInertia public

record TemporalReconstruction : Set₁ where
  constructor temporalReconstruction
  field
    Event : Set
    propositionTime discussionTime responseTime actionTime : Nat
    objectionTime revocationTime : Nat
    exactNode : Response.PropositionNode
    exactEpisode : Response.DecisionEpisode
    inertia : ProcessInertia
    subsequentActs : List Event

open TemporalReconstruction public

data TemporalClassification : Set where
  authorisedAndCompletedBeforeRevocation
  authorisedInitiallyStillUnfolding
  requiredClosureAfterRevocation
  newDiscretionaryPostRevocation
  recordingDiffersFromRecollection
  conditionalOrAmbiguousResponse : TemporalClassification

record ClassifiedTemporalReconstruction
  (reconstruction : TemporalReconstruction) : Set₁ where
  constructor classifiedTemporalReconstruction
  field
    classification : TemporalClassification
    classificationWitness : Set

open ClassifiedTemporalReconstruction public

------------------------------------------------------------------------
-- Proposition corruption dimensions.
------------------------------------------------------------------------

data CorruptionDimension : Set where
  parentToDescendant
  narrowToBroadContext
  considerToCommit
  boundedToIndefiniteScope
  openZeroToPositive
  earlierToLaterTime : CorruptionDimension

record PropositionCorruption : Set₁ where
  constructor propositionCorruption
  field
    sourceNode targetNode : Response.PropositionNode
    sourceEpisode targetEpisode : Response.DecisionEpisode
    sourceTime targetTime : Nat
    dimensions : List CorruptionDimension
    transportedWithoutWitness : Set

open PropositionCorruption public

record CorruptionBlocked : Set₁ where
  constructor corruptionBlocked
  field
    corruption : PropositionCorruption
    missingTransportWitness : Set

open CorruptionBlocked public

------------------------------------------------------------------------
-- Event and legal-character nodes remain separate.
------------------------------------------------------------------------

data LegalInterpretationNode : Set where
  physicalEventOccurred
  participantExperiencedDistress
  actWasInappropriate
  actIntendedToControl
  systematicCoercivePattern
  legalCharacterisation : LegalInterpretationNode

record LegalNodeResponse : Set where
  constructor legalNodeResponse
  field
    legalNode : LegalInterpretationNode
    stance : SSPTrit

open LegalNodeResponse public

record LegalPromotionWitness
  (source target : LegalInterpretationNode) : Set₁ where
  constructor legalPromotionWitness
  field
    evidentialBridge : Set
    typePromotionJustified : Set

-- There is no generic function from acknowledgement of occurrence, distress or
-- inappropriateness to acknowledgement of intention, pattern or legal class.

------------------------------------------------------------------------
-- The master proposition-indexed response object.
------------------------------------------------------------------------

record MasterRelationalResponse : Set₁ where
  constructor masterRelationalResponse
  field
    Participant : Set
    participant : Participant
    node : Response.PropositionNode
    episode : Response.DecisionEpisode
    time : Nat
    stance : SSPTrit
    zeroKind : Set
    capacity : Response.CapacityState
    transitionCone : Response.CounterfactualChoiceCone
    provenance : Response.ProvenanceKind
    unresolvedBoundary : Set

open MasterRelationalResponse public
