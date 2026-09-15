module DASHI.Biology.AnimalCommunicationSemanticEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC COMMUNICATION FUNCTION / SEMANTIC EVIDENCE LADDER
------------------------------------------------------------------------

data CommunicationEvidenceStage : Set where
  signalObserved : CommunicationEvidenceStage
  recurrentForm : CommunicationEvidenceStage
  contextAssociation : CommunicationEvidenceStage
  directedAddresseeAssociation : CommunicationEvidenceStage
  predictiveReceiverResponse : CommunicationEvidenceStage
  playbackInterventionResponse : CommunicationEvidenceStage
  supportedFunctionalReferenceClass : CommunicationEvidenceStage
  candidateCompositionalSemantics : CommunicationEvidenceStage

data PaymentStatus : Set where
  unpaid : PaymentStatus
  candidatePayment : PaymentStatus
  externallyPaid : PaymentStatus

data CommunicationSemanticDecision : Set where
  semanticUnresolved : CommunicationSemanticDecision
  semanticCandidate : CommunicationSemanticDecision
  semanticPromoted : CommunicationSemanticDecision
  semanticRejected : CommunicationSemanticDecision

record CommunicationEvidencePayment : Set where
  constructor communication-evidence-payment
  field
    repeatedProductionContext : PaymentStatus
    addresseeIdentityEvidence : PaymentStatus
    naturalReceiverResponse : PaymentStatus
    longitudinalInteractionHistory : PaymentStatus
    playbackOrInterventionEvidence : PaymentStatus
    publishedEthology : PaymentStatus
    sameObjectIdentity : PaymentStatus
    provenanceCustody : PaymentStatus
    independentAncestryCorroboration : PaymentStatus
    evidenceReferences : List String

open CommunicationEvidencePayment public

record CommunicationSemanticReceipt : Set where
  constructor communication-semantic-receipt
  field
    eventOrFamilyReference : String
    currentStage : CommunicationEvidenceStage
    humanReadableGloss : String
    evidencePayment : CommunicationEvidencePayment
    decision : CommunicationSemanticDecision
    sourceGenealogyReference : String
    preservesEarlierCandidateHistory : Bool
    canReopenOnContradiction : Bool

open CommunicationSemanticReceipt public

unpaidIllustrativeFoodRequest : CommunicationSemanticReceipt
unpaidIllustrativeFoodRequest = communication-semantic-receipt
  "no current animal event promoted"
  recurrentForm
  "food request (illustrative hypothesis only)"
  (communication-evidence-payment
    unpaid unpaid unpaid unpaid unpaid unpaid unpaid candidatePayment unpaid
    ("illustrative interaction-protocol hypothesis; no semantic payment" ∷ []))
  semanticUnresolved
  "no independent semantic genealogy paid"
  true
  true

record CommunicationSemanticBoundary : Set where
  constructor communication-semantic-boundary
  field
    responsePredictionDoesNotCreateMeaning : Bool
    functionalGlossDoesNotCreateAnimalIntent : Bool
    responseDoesNotCreatePromiseOrAgreement : Bool
    playbackEffectDoesNotCreatePropositionalMeaning : Bool
    modelGeneratedSignalDoesNotCreateKnownAnimalMeaning : Bool
    successfulOneOffInteractionDoesNotCreateStableProtocol : Bool
    rewardAssociationDoesNotCreatePropositionalNegotiation : Bool
    classifierConfidenceDoesNotCreateSemanticTruth : Bool
    publishedSourceDoesNotCreateAnimalexicPromotion : Bool
    semanticCandidateDoesNotCreateInterventionAuthority : Bool
    independentEvidenceCoordinatesRemainSeparate : Bool

open CommunicationSemanticBoundary public

canonicalCommunicationSemanticBoundary : CommunicationSemanticBoundary
canonicalCommunicationSemanticBoundary =
  communication-semantic-boundary
    true true true true true true true true true true true

record CommunicationSemanticReopeningPolicy : Set where
  constructor communication-semantic-reopening-policy
  field
    segmentationRevisionReopensFamilyMembership : Bool
    speciesIdentityRevisionReopensSpeciesTransfer : Bool
    senderAssignmentRevisionReopensInteractionClaim : Bool
    addresseeRevisionReopensDirectedMeaningClaim : Bool
    responseAssociationRevisionReopensFunctionalClaim : Bool
    contextRevisionReopensFunctionalInterpretation : Bool
    playbackContradictionReopensPromotion : Bool
    sourceGenealogyRevisionReopensIndependencePayment : Bool
    reopeningDoesNotErasePriorReceipt : Bool

open CommunicationSemanticReopeningPolicy public

canonicalCommunicationSemanticReopeningPolicy : CommunicationSemanticReopeningPolicy
canonicalCommunicationSemanticReopeningPolicy =
  communication-semantic-reopening-policy true true true true true true true true true
