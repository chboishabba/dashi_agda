module DASHI.Culture.AmyEskridgeVideoZoomClipSourceWeldExact where

-- Exact source-to-excerpt weld from the USER-ADMITTED video transcript
-- "She Researched Something THEY DON'T ALLOW. Then She Died", received
-- 2026-11-17. This is an editorial-source identity theorem, NOT verification
-- of the original speaker's allegations.
--
-- Original clip host: Zoom conversation featuring Amy Eskridge, Jeremy Rys,
-- and Mark Sokol. Original video at:
-- https://www.youtube.com/watch?v=l0O4cEIkUZc
-- Archival automatic transcript and video locator:
-- Blocked Epistemology, "[Archive] - Amy Eskridge Zoom", 2024-01-27
-- https://blockedepistemology.substack.com/p/archive-amy-eskridge-zoom
-- Archived transcript timestamps below belong to the ORIGINAL >3h source,
-- not to the edited video. Archive author explicitly does not endorse
-- transcript content. Source proposition role is "Amy reported/recounted",
-- NEVER an externally inspected NSA, surveillance, or physics fact.
-- The video is a spliced montage: the first 00:21 rearranges original
-- source chronology (35:40 then 31:02 then 34:18).
--
-- Repo existing primary provenance owner:
-- DASHI.Culture.AmyEskridgeOSINTSnowballExact.archivedAmyInterviewSource
-- Repo video-claim owner: AmyEskridgeVideoClaimAttributionLedgerExact
-- Policy: Docs/SourceAttributionPolicy.md.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as A
import DASHI.Culture.AmyEskridgeOSINTSnowballExact as OSINT
import DASHI.Culture.AmyEskridgeVideoClaimAttributionLedgerExact as Video

data ClipEvidenceRole : Set where
  directSpeakerAttribution : ClipEvidenceRole
  speakerRetellingOfUninspectedInformant : ClipEvidenceRole
  allegationNotEventVerification : ClipEvidenceRole

record ExactClipJoin : Set where
  constructor exact-clip-join
  field
    videoClaim : Video.RawAttributedClaim
    originalRecording : A.AttributedSource
    editedVideoTime : String
    originalRecordingTime : String
    clipRole : ClipEvidenceRole
    boundedReading : String
    remainsUnpaid : String

open ExactClipJoin public

openingThreat : ExactClipJoin
openingThreat = exact-clip-join Video.claim001 OSINT.archivedAmyInterviewSource
  "00:00-00:06" "35:40-35:53"
  speakerRetellingOfUninspectedInformant
  "Amy reports hearing threatening statements; the edited clip starts here"
  "Uncut clip identity is found; original threatening person(s), actual threat events, alleged government agency and independent corroboration remain unknown"

nsaFive : ExactClipJoin
nsaFive = exact-clip-join Video.claim002 OSINT.archivedAmyInterviewSource
  "00:05-00:11" "30:44-31:22"
  speakerRetellingOfUninspectedInformant
  "Amy attributes an alleged NSA list of five antigravity discoverers to an external alleged secret-space-program contact, not to a document she personally inspected"
  "No authenticated NSA roster, official records or independent technical discovery"

fourSuppressions : ExactClipJoin
fourSuppressions = exact-clip-join Video.claim003 OSINT.archivedAmyInterviewSource
  "00:11-00:21" "34:18-34:38"
  speakerRetellingOfUninspectedInformant
  "Amy quotes the same contact's allegation that four earlier discoveries were suppressed"
  "Named independently demonstrated antigravity technologies, suppression acts and actor identity all remain unpaid"

lexusSurveillance : ExactClipJoin
lexusSurveillance = exact-clip-join Video.claim005 OSINT.archivedAmyInterviewSource
  "00:31-01:23" "2:53:41-2:56:11"
  directSpeakerAttribution
  "Amy reports believing she was physically surveilled following residential incidents"
  "Original audiovisual report is not independent evidence of who watched, why, or any link to her death"

lexusVehicle : ExactClipJoin
lexusVehicle = exact-clip-join Video.claim006 OSINT.archivedAmyInterviewSource
  "00:36-01:23" "2:54:11-2:56:11"
  directSpeakerAttribution
  "Amy reports a dark-window silver Lexus and changing licence plates"
  "No independent dated plate registry, photo, incident report or verified occupant"

lexusPlateChange : ExactClipJoin
lexusPlateChange = exact-clip-join Video.claim007 OSINT.archivedAmyInterviewSource
  "01:03-01:23" "2:55:05-2:56:11"
  directSpeakerAttribution
  "Amy reports seeing an individual change a vehicle's registration plate"
  "No independent recording, lawful registration evidence or actor/agency attribution"

futureP52 : ExactClipJoin
futureP52 = exact-clip-join Video.claim010 OSINT.archivedAmyInterviewSource
  "01:41-01:53" "52:22-52:59"
  directSpeakerAttribution
  "Amy speaks of P47/P52 future humans; the edited video excerpts her P52 statement"
  "The unedited recording is a source of her statement, not evidence of time travel"

exactAmyClipJoins : List ExactClipJoin
exactAmyClipJoins =
  openingThreat ∷ nsaFive ∷ fourSuppressions ∷ lexusSurveillance ∷
  lexusVehicle ∷ lexusPlateChange ∷ futureP52 ∷ []

-- Repo-native edit-order check, narrowest unit = minute of source recording.
-- Original temporal order is NSA at 31, suppression at 34, threats at 35.
-- Edited video's initial order is threats, NSA, suppression.
-- The strictly descending first splice is source backed by timestamps.
atMost : Nat → Nat → Bool
atMost zero _ = true
atMost (suc _) zero = false
atMost (suc n) (suc m) = atMost n m

nsaBeforeFourSuppressions : atMost 31 34 ≡ true
nsaBeforeFourSuppressions = refl

suppressionBeforeThreat : atMost 34 35 ≡ true
suppressionBeforeThreat = refl

editedFirstClipIsChronologicallyLater : atMost 35 31 ≡ false
editedFirstClipIsChronologicallyLater = refl

-- Explicitly forbid automatic promotion via the source registry alone.
data FirsthandStatementIsOfficialNSARecord : Set where
data FirsthandStatementIsVerifiedSurveillance : Set where
data FirsthandStatementIsScientificProof : Set where
