module DASHI.Cognition.PNF.SensibLawClaimLatticeNarrativeStatusLiveBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import ClaimReconciliationObjectLattice as Claims
import DASHI.Cognition.PNF.NarrativeClaimProvenanceExact as Narrative
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status

------------------------------------------------------------------------
-- LIVE CLAIM-LATTICE -> STATUS BIDI
--
-- This owner reuses the older affidavit/claim reconciliation lattice as an
-- actual producer of discourse status.  It does not reuse its free-form text
-- fields as regex/lexical semantic authority: only its already-typed claim
-- classifications and promotion-separation proofs may populate status axes.
------------------------------------------------------------------------

claimPropositionStatus : Claims.PropositionType → Status.PropositionStatus
claimPropositionStatus Claims.factualEvent = Status.assertedBySource
claimPropositionStatus Claims.subjectiveFeeling = Status.assertedBySource
claimPropositionStatus Claims.allegation = Status.allegedProposition
claimPropositionStatus Claims.denial = Status.deniedProposition
claimPropositionStatus Claims.proceduralFact = Status.assertedBySource
claimPropositionStatus Claims.legalClaim = Status.assertedBySource
claimPropositionStatus Claims.relationshipState = Status.assertedBySource
claimPropositionStatus Claims.capabilityStatement = Status.assertedBySource
claimPropositionStatus Claims.careOrRolePerformance = Status.assertedBySource
claimPropositionStatus Claims.typedObjectClaim = Status.assertedBySource

claimAtomProposition : Claims.ClaimAtom → Status.PropositionStatusProduct
claimAtomProposition claim =
  Status.propositionStatusProduct
    (Claims.propositionId claim)
    (claimPropositionStatus (Claims.propositionType claim))
    Status.truthUnresolved
    Status.propositionSource
    Status.evidenceNeutral
    Status.sourceEvidence
    Status.modalityKindUnresolved
    Status.modalForceUnresolved
    Status.scopeUnresolved

claimAtomTruthRemainsUnresolved :
  (claim : Claims.ClaimAtom) →
  Status.truthStatus (claimAtomProposition claim) ≡ Status.truthUnresolved
claimAtomTruthRemainsUnresolved claim = refl

------------------------------------------------------------------------
-- Occurrence requires a stricter, indexed reading.  Not every ClaimAtom is an
-- eventuality claim.  The constructors below are the only generic promotion
-- paths provided here.
------------------------------------------------------------------------

data ClaimOccurrenceReading :
    Claims.PropositionType → Status.OccurrenceStatus → Set where
  factualEventReading :
    ClaimOccurrenceReading Claims.factualEvent Status.assertedOccurrence
  allegationReading :
    ClaimOccurrenceReading Claims.allegation Status.allegedOccurrence
  denialReading :
    ClaimOccurrenceReading Claims.denial Status.deniedOccurrence

record LiveClaimOccurrenceReceipt (claim : Claims.ClaimAtom) : Set where
  constructor liveClaimOccurrenceReceipt
  field
    eventReference : String
    resultingOccurrence : Status.OccurrenceStatus
    reading :
      ClaimOccurrenceReading (Claims.propositionType claim) resultingOccurrence
    eventStatus : Status.EventStatusProduct
    sameEventReference :
      Status.eventReference eventStatus ≡ eventReference
    sameOccurrence :
      Status.occurrence eventStatus ≡ resultingOccurrence
    sourcePromotionStillFalse :
      Claims.claimPromotionState claim ≡ Claims.Relation.promotionFalse

open LiveClaimOccurrenceReceipt public

makeLiveClaimOccurrenceReceipt :
  (claim : Claims.ClaimAtom) →
  (eventRef : String) →
  (occurrence : Status.OccurrenceStatus) →
  ClaimOccurrenceReading (Claims.propositionType claim) occurrence →
  LiveClaimOccurrenceReceipt claim
makeLiveClaimOccurrenceReceipt claim eventRef occurrence reading =
  liveClaimOccurrenceReceipt
    eventRef
    occurrence
    reading
    (Status.eventStatusProduct
      eventRef occurrence Status.eventTime Status.scopeUnresolved)
    refl
    refl
    (Claims.claimPromotionStateIsFalse claim)

canonicalDogWalkedOccurrence :
  LiveClaimOccurrenceReceipt Claims.canonicalDogWalkedClaim
canonicalDogWalkedOccurrence =
  makeLiveClaimOccurrenceReceipt
    Claims.canonicalDogWalkedClaim
    "event:dog-walk"
    Status.assertedOccurrence
    factualEventReading

canonicalDogDeniedOccurrence :
  LiveClaimOccurrenceReceipt Claims.canonicalDogNotWalkedClaim
canonicalDogDeniedOccurrence =
  makeLiveClaimOccurrenceReceipt
    Claims.canonicalDogNotWalkedClaim
    "event:dog-walk"
    Status.deniedOccurrence
    denialReading

------------------------------------------------------------------------
-- NarrativeClaimProvenance gives a second, generic discriminator.  Its modality
-- changes proposition/evidence status, but never manufactures truth.
------------------------------------------------------------------------

narrativePropositionStatus : Narrative.ClaimModality → Status.PropositionStatus
narrativePropositionStatus Narrative.alleged = Status.allegedProposition
narrativePropositionStatus Narrative.denied = Status.deniedProposition
narrativePropositionStatus Narrative.corroborated = Status.propositionRepresented
narrativePropositionStatus Narrative.refuted = Status.rejectedProposition
narrativePropositionStatus Narrative.unresolved = Status.propositionUnresolved
narrativePropositionStatus Narrative.interpreted = Status.propositionRepresented

narrativeEvidencePolarity : Narrative.ClaimModality → Status.EvidencePolarity
narrativeEvidencePolarity Narrative.alleged = Status.evidenceNeutral
narrativeEvidencePolarity Narrative.denied = Status.evidenceAgainst
narrativeEvidencePolarity Narrative.corroborated = Status.evidenceFor
narrativeEvidencePolarity Narrative.refuted = Status.evidenceAgainst
narrativeEvidencePolarity Narrative.unresolved = Status.evidencePolarityUnresolved
narrativeEvidencePolarity Narrative.interpreted = Status.evidenceNeutral

narrativeOccurrenceStatus : Narrative.ClaimModality → Status.OccurrenceStatus
narrativeOccurrenceStatus Narrative.alleged = Status.allegedOccurrence
narrativeOccurrenceStatus Narrative.denied = Status.deniedOccurrence
narrativeOccurrenceStatus Narrative.corroborated = Status.reportedOccurrence
narrativeOccurrenceStatus Narrative.refuted = Status.questionedOccurrence
narrativeOccurrenceStatus Narrative.unresolved = Status.occurrenceUnresolved
narrativeOccurrenceStatus Narrative.interpreted = Status.mentionedEventuality

record NarrativeModalityStatusReceipt : Set where
  constructor narrativeModalityStatusReceipt
  field
    propositionReference : String
    eventReference : String
    modality : Narrative.ClaimModality
    proposition : Status.PropositionStatusProduct
    event : Status.EventStatusProduct
    propositionStatusExact :
      Status.propositionStatus proposition ≡ narrativePropositionStatus modality
    occurrenceStatusExact :
      Status.occurrence event ≡ narrativeOccurrenceStatus modality
    truthStillUnresolved :
      Status.truthStatus proposition ≡ Status.truthUnresolved

open NarrativeModalityStatusReceipt public

compileNarrativeModality :
  String → String → Narrative.ClaimModality → NarrativeModalityStatusReceipt
compileNarrativeModality propositionRef eventRef modality =
  narrativeModalityStatusReceipt
    propositionRef
    eventRef
    modality
    (Status.propositionStatusProduct
      propositionRef
      (narrativePropositionStatus modality)
      Status.truthUnresolved
      Status.propositionSource
      (narrativeEvidencePolarity modality)
      Status.provenanceEvidence
      Status.modalityKindUnresolved
      Status.modalForceUnresolved
      Status.scopeUnresolved)
    (Status.eventStatusProduct
      eventRef
      (narrativeOccurrenceStatus modality)
      Status.eventTime
      Status.scopeUnresolved)
    refl
    refl
    refl

------------------------------------------------------------------------
-- Hard boundaries recovered from the historical owners.
------------------------------------------------------------------------

data CorroborationAutomaticallyAdmitsTruth : Set where
data RefutationAutomaticallyAdmitsFalsity : Set where
data ClaimTypeAloneAdmitsOccurrence : Set where
data DenialIsSemanticNegation : Set where

corroborationDoesNotAutoAdmitTruth : CorroborationAutomaticallyAdmitsTruth → ⊥
corroborationDoesNotAutoAdmitTruth ()

refutationDoesNotAutoAdmitFalsity : RefutationAutomaticallyAdmitsFalsity → ⊥
refutationDoesNotAutoAdmitFalsity ()

claimTypeAloneDoesNotAdmitOccurrence : ClaimTypeAloneAdmitsOccurrence → ⊥
claimTypeAloneDoesNotAdmitOccurrence ()

denialDoesNotCollapseToNegation : DenialIsSemanticNegation → ⊥
denialDoesNotCollapseToNegation ()
