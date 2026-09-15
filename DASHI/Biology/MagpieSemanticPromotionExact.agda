module DASHI.Biology.MagpieSemanticPromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.MagpieVocalAtlasObservationExact as Observation
import DASHI.Biology.MagpieVocalAtlasLatentExact as Latent

------------------------------------------------------------------------
-- MAGPIE SEMANTIC PROMOTION
--
-- Human-readable words such as "hello", "danger" or "food here" are late
-- interpretations.  This owner records the payment ladder and reopening
-- boundaries; it does not assert that any current magpie event has such a
-- meaning.
------------------------------------------------------------------------

data SemanticPromotionStage : Set where
  observedEvent : SemanticPromotionStage
  candidateCluster : SemanticPromotionStage
  crossRecordingMotif : SemanticPromotionStage
  contextAssociatedFamily : SemanticPromotionStage
  crossGroupFunctionalFamily : SemanticPromotionStage
  candidateSemanticInvariant : SemanticPromotionStage
  validatedFunctionalReferentialClass : SemanticPromotionStage

data PaymentStatus : Set where
  unpaid : PaymentStatus
  candidatePayment : PaymentStatus
  externallyPaid : PaymentStatus

data SemanticDecision : Set where
  semanticUnresolved : SemanticDecision
  semanticCandidate : SemanticDecision
  semanticPromoted : SemanticDecision
  semanticRejected : SemanticDecision

record SemanticEvidencePayment : Set where
  constructor semantic-evidence-payment
  field
    repeatedProductionContext : PaymentStatus
    receiverResponse : PaymentStatus
    longitudinalWithinGroupUse : PaymentStatus
    playbackOrInterventionEvidence : PaymentStatus
    publishedEthology : PaymentStatus
    sourceProvenance : PaymentStatus
    sameObjectIdentity : PaymentStatus
    independentAncestry : PaymentStatus
    evidenceReferences : List String

open SemanticEvidencePayment public

record SemanticPromotionReceipt : Set where
  constructor semantic-promotion-receipt
  field
    eventOrFamilyReference : String
    currentStage : SemanticPromotionStage
    candidateHumanLabel : String
    evidencePayment : SemanticEvidencePayment
    decision : SemanticDecision
    sourceGenealogyReference : String
    preservesEarlierCandidateHistory : Bool
    canReopenOnContradiction : Bool

open SemanticPromotionReceipt public

unpaidHelloCandidate : SemanticPromotionReceipt
unpaidHelloCandidate = semantic-promotion-receipt
  "no current event promoted"
  candidateCluster
  "hello (illustrative hypothesis only)"
  (semantic-evidence-payment
    unpaid unpaid unpaid unpaid unpaid candidatePayment unpaid unpaid
    ("design hypothesis; no real magpie semantic payment" ∷ []))
  semanticUnresolved
  "no independent semantic genealogy paid"
  true
  true

record SemanticPromotionBoundary : Set where
  constructor semantic-promotion-boundary
  field
    acousticSimilarityAloneCreatesSemanticTruth : Bool
    classifierConfidenceCreatesSemanticTruth : Bool
    sourceTitleCreatesSemanticTruth : Bool
    semanticCandidateDoesNotCreateInterventionAuthority : Bool
    modelPredictionDoesNotCreateAnimalIntent : Bool
    repeatedSelfPredictionDoesNotCreateIndependentCorroboration : Bool
    receiverResponseEvidenceIsIndependentCoordinate : Bool
    playbackEvidenceIsIndependentCoordinate : Bool
    crossPopulationRecurrenceAloneCreatesReferentialMeaning : Bool
    laterEvidenceMayReopenSemanticPromotion : Bool
    earlierCandidateHistoryRemainsAppendOnly : Bool
    semanticPromotionDoesNotCreateConsentOrPromise : Bool

open SemanticPromotionBoundary public

canonicalSemanticPromotionBoundary : SemanticPromotionBoundary
canonicalSemanticPromotionBoundary =
  semantic-promotion-boundary
    false false false true true true true true false true true true

record SemanticReopeningPolicy : Set where
  constructor semantic-reopening-policy
  field
    segmentationRevisionReopensFamilyMembership : Bool
    speciesIdentityRevisionReopensCrossPopulationClaim : Bool
    individualOrGroupRevisionReopensSocialLearningClaim : Bool
    locationRevisionReopensDialectClaim : Bool
    recordingConfoundReopensGeographicRealisation : Bool
    contextRevisionReopensFunctionalInterpretation : Bool
    receiverResponseContradictionReopensSemanticPromotion : Bool
    sourceGenealogyRevisionReopensIndependencePayment : Bool
    reopeningDoesNotErasePriorReceipt : Bool

open SemanticReopeningPolicy public

canonicalSemanticReopeningPolicy : SemanticReopeningPolicy
canonicalSemanticReopeningPolicy =
  semantic-reopening-policy true true true true true true true true true

observationOwnerReused : String
observationOwnerReused = "DASHI.Biology.MagpieVocalAtlasObservationExact"

latentOwnerReused : String
latentOwnerReused = "DASHI.Biology.MagpieVocalAtlasLatentExact"

semanticPromotionReading : String
semanticPromotionReading =
  "A human-readable magpie meaning is a staged evidence claim, not a nearest-neighbour label. Repeated context, receiver response, longitudinal group use, intervention/playback evidence, published ethology, same-object identity, provenance and independent ancestry remain separately payable. Candidate semantics create neither intervention authority nor claims about animal intent, consent, promises or agreements."
