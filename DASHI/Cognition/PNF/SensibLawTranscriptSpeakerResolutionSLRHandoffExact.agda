module DASHI.Cognition.PNF.SensibLawTranscriptSpeakerResolutionSLRHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTranscriptSpeakerResolutionExact as Speaker

------------------------------------------------------------------------
-- Runtime/SLR handoff contract.
--
-- The runtime may parse text, build PNF/discourse/world-model features and emit
-- candidate rankings.  DASHI owns semantic admission.  Raw source identity and
-- inferred identity therefore remain separate coordinates.
------------------------------------------------------------------------

record SLRTranscriptTurn : Set where
  constructor slrTranscriptTurn
  field
    claimReference : String
    rawSpeakerLabel : String
    rawTextReference : String
    precedingClaimReference : String
    followingClaimReference : String
    sourceArtifactReference : String

open SLRTranscriptTurn public

record SLRSpeakerCandidateOutput : Set where
  constructor slrSpeakerCandidateOutput
  field
    turn : SLRTranscriptTurn
    features : Speaker.SpeakerFeatureVector
    proposedSpeaker : Speaker.SpeakerCandidate
    proposedStatus : Speaker.SpeakerResolutionStatus
    runtimeModelReference : String
    runtimeReceiptReference : String

open SLRSpeakerCandidateOutput public

record SpeakerPromotionReceipt : Set where
  constructor speakerPromotionReceipt
  field
    candidateOutputReference : String
    exactSourceReference : String
    exactSpeakerReference : String
    promotedStatus : Speaker.SpeakerResolutionStatus
    promotionRationale : String

open SpeakerPromotionReceipt public

record SLRSpeakerResolutionBoundary : Set where
  constructor slrSpeakerResolutionBoundary
  field
    runtimeMayEmitCandidate : Bool
    runtimeMayEmitCandidateIsTrue : runtimeMayEmitCandidate ≡ true
    runtimeMayEmitLikely : Bool
    runtimeMayEmitLikelyIsTrue : runtimeMayEmitLikely ≡ true
    runtimeMayOverwriteRawSpeakerLabel : Bool
    runtimeMayOverwriteRawSpeakerLabelIsFalse : runtimeMayOverwriteRawSpeakerLabel ≡ false
    runtimeMaySelfIssueVerifiedPromotion : Bool
    runtimeMaySelfIssueVerifiedPromotionIsFalse : runtimeMaySelfIssueVerifiedPromotion ≡ false
    sourceReceiptMayPromoteVerified : Bool
    sourceReceiptMayPromoteVerifiedIsTrue : sourceReceiptMayPromoteVerified ≡ true

canonicalSLRSpeakerResolutionBoundary : SLRSpeakerResolutionBoundary
canonicalSLRSpeakerResolutionBoundary =
  slrSpeakerResolutionBoundary true refl true refl false refl false refl true refl

------------------------------------------------------------------------
-- C032 concrete handoff.
------------------------------------------------------------------------

c032Turn : SLRTranscriptTurn
c032Turn = slrTranscriptTurn
  "ABC730-2026-09-09-C032"
  "speaker unresolved in supplied transcript"
  "This is unbelievable gaslighting from Labor"
  "ABC730-2026-09-09-C031"
  "ABC730-2026-09-09-C033"
  "user-supplied ABC 7.30 transcript, 9 September 2026"

c032WitnessSeed : Speaker.SpeakerResolutionPacket
c032WitnessSeed = Speaker.c032LikelyShoebridge

fixtureReference : String
fixtureReference = "fixtures/slr/abc730-west-bank-sanctions-2026-09-09-speaker-resolution.jsonl"
