module DASHI.Cognition.PNF.SensibLawTranscriptSpeakerResolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Attribution

------------------------------------------------------------------------
-- Speaker-resolution seam for transcript ingestion.
--
-- This layer sits before ClaimAttributionOccurrenceWeld.  It permits parser,
-- discourse, world-model, user-witness and source evidence to rank candidate
-- speakers without silently converting a candidate into verified attribution.
------------------------------------------------------------------------

data SpeakerEvidenceKind : Set where
  transcriptLabel : SpeakerEvidenceKind
  visualLowerThird : SpeakerEvidenceKind
  officialTranscript : SpeakerEvidenceKind
  sameDayPublishedQuote : SpeakerEvidenceKind
  userWitness : SpeakerEvidenceKind
  discourseContext : SpeakerEvidenceKind
  worldModelCandidate : SpeakerEvidenceKind
  lexicalStyleCandidate : SpeakerEvidenceKind

data SpeakerResolutionStatus : Set where
  unresolved : SpeakerResolutionStatus
  candidate : SpeakerResolutionStatus
  likely : SpeakerResolutionStatus
  verified : SpeakerResolutionStatus

data SpeakerCandidate : Set where
  sarahFerguson : SpeakerCandidate
  davidShoebridge : SpeakerCandidate
  edHusic : SpeakerCandidate
  julianLeeser : SpeakerCandidate
  pennyWong : SpeakerCandidate
  emilyThornberry : SpeakerCandidate
  otherSpeaker : String → SpeakerCandidate

record SpeakerEvidence : Set where
  constructor speakerEvidence
  field
    candidateSpeaker : SpeakerCandidate
    evidenceKind : SpeakerEvidenceKind
    evidenceReference : String
    boundedDescription : String

open SpeakerEvidence public

record SpeakerResolutionPacket : Set where
  constructor speakerResolutionPacket
  field
    claimReference : String
    rawSpeakerLabel : String
    proposedSpeaker : SpeakerCandidate
    status : SpeakerResolutionStatus
    supportingEvidence : SpeakerEvidence
    sourcePromotionRequired : Bool
    residual : String

open SpeakerResolutionPacket public

------------------------------------------------------------------------
-- ABC 7.30 9-Sep-2026 fixture.
------------------------------------------------------------------------

c032ShoebridgeUserWitness : SpeakerEvidence
c032ShoebridgeUserWitness = speakerEvidence
  davidShoebridge
  userWitness
  "user eyewitness recollection from ABC 7.30 broadcast; user subsequently located related Greens material but has not supplied exact source span"
  "The user reports seeing David Shoebridge deliver the 'unbelievable gaslighting from Labor' line on television. This is admissible as a likely-speaker witness, not as independent source verification."

c032LikelyShoebridge : SpeakerResolutionPacket
c032LikelyShoebridge = speakerResolutionPacket
  "ABC730-2026-09-09-C032"
  "speaker unresolved in supplied transcript"
  davidShoebridge
  likely
  c032ShoebridgeUserWitness
  true
  "promote to verified only on visual lower-third, official clip/caption, same-day Greens publication carrying the utterance, or equivalent exact source receipt"

c030HusicCandidate : SpeakerResolutionPacket
c030HusicCandidate = speakerResolutionPacket
  "ABC730-2026-09-09-C030"
  "progressive/backbench voice"
  edHusic
  candidate
  (speakerEvidence edHusic sameDayPublishedQuote
    "same-day public reporting aligns the preceding Palestinian-state/settlements proposition with Ed Husic"
    "Candidate is externally corroborated but should still be welded to the exact ABC cut before verified promotion.")
  true
  "recover exact ABC cut or lower-third"

c033LeeserCandidate : SpeakerResolutionPacket
c033LeeserCandidate = speakerResolutionPacket
  "ABC730-2026-09-09-C033"
  "government-defending voice"
  julianLeeser
  candidate
  (speakerEvidence julianLeeser sameDayPublishedQuote
    "same-day public reporting aligns the two-state/sanctions-effectiveness proposition with Julian Leeser"
    "Candidate is externally corroborated but exact ABC same-object attribution remains a distinct receipt.")
  true
  "recover exact ABC cut or lower-third"

------------------------------------------------------------------------
-- Parser/world-model candidate output.
------------------------------------------------------------------------

record SpeakerFeatureVector : Set where
  constructor speakerFeatureVector
  field
    claimReference : String
    candidateSpeaker : SpeakerCandidate
    lexicalCompatibility : Bool
    topicPositionCompatibility : Bool
    neighbouringTurnCompatibility : Bool
    sameDayPublicStatementCompatibility : Bool
    visualIdentityCompatibility : Bool
    sourceIdentityCompatibility : Bool
    featureProvenance : String

open SpeakerFeatureVector public

record SpeakerInferenceProposal : Set where
  constructor speakerInferenceProposal
  field
    features : SpeakerFeatureVector
    proposedStatus : SpeakerResolutionStatus
    inferenceReference : String

open SpeakerInferenceProposal public

------------------------------------------------------------------------
-- Admission boundary.
------------------------------------------------------------------------

record SpeakerAdmissionBoundary : Set where
  constructor speakerAdmissionBoundary
  field
    userWitnessMaySupportLikely : Bool
    userWitnessMaySupportLikelyIsTrue : userWitnessMaySupportLikely ≡ true
    modelCandidateMaySelfPromoteVerified : Bool
    modelCandidateMaySelfPromoteVerifiedIsFalse : modelCandidateMaySelfPromoteVerified ≡ false
    discourseCompatibilityProvesIdentity : Bool
    discourseCompatibilityProvesIdentityIsFalse : discourseCompatibilityProvesIdentity ≡ false
    verifiedSpeakerProvesPropositionTruth : Bool
    verifiedSpeakerProvesPropositionTruthIsFalse : verifiedSpeakerProvesPropositionTruth ≡ false

canonicalSpeakerAdmissionBoundary : SpeakerAdmissionBoundary
canonicalSpeakerAdmissionBoundary = speakerAdmissionBoundary true refl false refl false refl false refl

------------------------------------------------------------------------
-- Existing PNF attribution weld remains downstream owner once identity is paid.
------------------------------------------------------------------------

data SpeakerResolutionIsAttributionWeld : Set where

speakerResolutionDoesNotByItselfWeld : SpeakerResolutionIsAttributionWeld → ⊥
speakerResolutionDoesNotByItselfWeld ()

attributionOwnerReference : String
attributionOwnerReference =
  "DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact.ClaimAttributionOccurrenceWeld"
