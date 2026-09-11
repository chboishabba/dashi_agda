module DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as Transcript

------------------------------------------------------------------------
-- Primary-source speaker-resolution overlay.
--
-- The supplied transcript ledger remains append-only.  This owner records a
-- later, stronger source: ABC's own published 7.30 transcript for the same
-- programme object.  It may pay speaker attribution for claims whose wording
-- can be aligned to explicitly labelled ABC transcript turns; it does not
-- rewrite the historical supplied-transcript state.
------------------------------------------------------------------------

data ResolutionStatus : Set where
  sourcePaid : ResolutionStatus
  sourceContradicted : ResolutionStatus
  sourceUnresolved : ResolutionStatus

record PrimarySourceReceipt : Set where
  constructor primarySourceReceipt
  field
    sourceId : String
    sourceTitle : String
    publisher : String
    publicationDate : String
    sourceUrl : String
    sameProgrammeObjectReference : String
    speakerLabelledTranscript : Bool

open PrimarySourceReceipt public

abcPublishedTranscript : PrimarySourceReceipt
abcPublishedTranscript = primarySourceReceipt
  "ABC-107135268"
  "New sanctions placed on Israeli settlements"
  "ABC News / 7.30"
  "2026-09-09"
  "https://www.abc.net.au/news/2026-09-09/new-sanctions-placed-on-israeli-settlements-/107135268"
  "ABC 7.30 segment dated 2026-09-09; same wording sequence as supplied transcript claim surface"
  true

record ClaimSpeakerResolution : Set where
  constructor claimSpeakerResolution
  field
    claimReference : String
    canonicalClaimReference : String
    resolvedSpeaker : String
    status : ResolutionStatus
    primarySourceReference : String
    labelledTurnReference : String
    suppliedTranscriptStateRewritten : Bool
    propositionTruthPromoted : Bool

open ClaimSpeakerResolution public

c030SpeakerResolution : ClaimSpeakerResolution
c030SpeakerResolution = claimSpeakerResolution
  "ABC730-2026-09-09-C030"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c030"
  "Ed Husic"
  sourcePaid
  "ABC-107135268"
  "ED HUSIC, LABOR MP: We can't say we are for the state of Palestine ... illegal settlements are undermining ..."
  false false

c031SpeakerResolution : ClaimSpeakerResolution
c031SpeakerResolution = claimSpeakerResolution
  "ABC730-2026-09-09-C031"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c031"
  "Ed Husic"
  sourcePaid
  "ABC-107135268"
  "ED HUSIC, LABOR MP: ... We need to take action."
  false false

c032SpeakerResolution : ClaimSpeakerResolution
c032SpeakerResolution = claimSpeakerResolution
  "ABC730-2026-09-09-C032"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c032"
  "David Shoebridge"
  sourcePaid
  "ABC-107135268"
  "DAVID SHOEBRIDGE, GREENS SENATOR: The reason why they're not taking action ... unbelievable gaslighting from Labor."
  false false

c033SpeakerResolution : ClaimSpeakerResolution
c033SpeakerResolution = claimSpeakerResolution
  "ABC730-2026-09-09-C033"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c033"
  "Julian Leeser"
  sourcePaid
  "ABC-107135268"
  "JULIAN LEESER, LIBERAL FRONTBENCHER: The key thing ... is a two-state solution ... whether any of these sanctions actually lead you towards a two-state solution ..."
  false false

resolvedFrontier : List ClaimSpeakerResolution
resolvedFrontier =
  c030SpeakerResolution ∷ c031SpeakerResolution ∷ c032SpeakerResolution ∷ c033SpeakerResolution ∷ []

------------------------------------------------------------------------
-- Named competing hypothesis from the earlier consumer.
------------------------------------------------------------------------

bandtC032Resolution : ClaimSpeakerResolution
bandtC032Resolution = claimSpeakerResolution
  "ABC730-2026-09-09-C032"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c032"
  "Adam Bandt"
  sourceContradicted
  "ABC-107135268"
  "ABC labels DAVID SHOEBRIDGE, GREENS SENATOR as the speaker of the gaslighting line."
  false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LaterPrimarySourceRewritesHistoricalTranscriptState : Set where
laterPrimarySourceDoesNotRewriteHistoricalTranscriptState : LaterPrimarySourceRewritesHistoricalTranscriptState → ⊥
laterPrimarySourceDoesNotRewriteHistoricalTranscriptState ()

data SpeakerResolutionPromotesEvaluativeTruth : Set where
speakerResolutionDoesNotPromoteEvaluativeTruth : SpeakerResolutionPromotesEvaluativeTruth → ⊥
speakerResolutionDoesNotPromoteEvaluativeTruth ()

data SpeakerResolutionPromotesPolicyCorrectness : Set where
speakerResolutionDoesNotPromotePolicyCorrectness : SpeakerResolutionPromotesPolicyCorrectness → ⊥
speakerResolutionDoesNotPromotePolicyCorrectness ()

record PrimarySourceResolutionBoundary : Set where
  constructor primarySourceResolutionBoundary
  field
    suppliedTranscriptStateRemainsAppendOnly : Bool
    primaryTranscriptMayPaySpeakerIdentity : Bool
    sameObjectAlignmentRequired : Bool
    speakerIdentityDoesNotPayEvaluativeTruth : Bool
    contradictoryNamedSpeakerHypothesisMayBeRejected : Bool

canonicalPrimarySourceResolutionBoundary : PrimarySourceResolutionBoundary
canonicalPrimarySourceResolutionBoundary =
  primarySourceResolutionBoundary true true true true true

canonicalGaslightingClaim : Transcript.TranscriptClaim
canonicalGaslightingClaim = Transcript.abcLaborGaslightingClaim
