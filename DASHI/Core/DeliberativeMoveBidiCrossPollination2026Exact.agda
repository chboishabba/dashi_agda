module DASHI.Core.DeliberativeMoveBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

------------------------------------------------------------------------
-- DELIBERATIVE MOVE -- BIDI CROSS-POLLINATION
--
-- Source calibration:
-- Bartlett, Cheryl; Marshall, Murdena; Marshall, Albert (2012),
-- "Two-Eyed Seeing and other lessons learned within a co-learning journey of
-- bringing together indigenous and mainstream knowledges and ways of knowing",
-- Journal of Environmental Studies and Sciences 2:331-340,
-- DOI 10.1007/s13412-012-0086-8.
--
-- Repository donor:
-- DASHI.Core.HistoryIndexedProofExperimentActionLoopExact (merged PR #697).
--
-- DASHI extension only: the existing think/look/test/act controller can be
-- widened with ask/listen/deliberate moves for residuals whose missing state is
-- held by another situated participant or whose proposal itself may be revised.
-- This is not asserted as a universal description of Indigenous governance.
------------------------------------------------------------------------

data EpistemicMoveKind : Set where
  thinkMove lookMove testMove askMove listenMove deliberateMove actMove : EpistemicMoveKind

data DeliberationOutcome : Set where
  consensusReached legitimateResidualDisagreement proposalRevised moreHearingRequired : DeliberationOutcome

record SituatedParticipant : Set where
  constructor situated-participant
  field
    participantReference : String
    authorityReference : String
    permissionReference : String

open SituatedParticipant public

record Objection : Set where
  constructor objection
  field
    objector : SituatedParticipant
    objectionReference : String
    affectedInterestReference : String
    serious : Bool

open Objection public

record DeliberativeMove : Set where
  constructor deliberative-move
  field
    moveKind : EpistemicMoveKind
    residualReference : String
    participantReference : String
    authorityReceiptReference : String
    expectedInformationGainReference : String

open DeliberativeMove public

record ReopenOnSeriousObjection : Set where
  constructor reopen-on-serious-objection
  field
    objection : Objection
    seriousIsTrue : serious objection ≡ true
    reopenedResidualReference : String
    reformulationReference : String

open ReopenOnSeriousObjection public

------------------------------------------------------------------------
-- Asking/listening/deliberating are not synonyms for passive observation or
-- physical execution.
------------------------------------------------------------------------

data ListeningEqualsAuthorityTransfer : Set where
data HearingEqualsAgreement : Set where
data ObjectionEqualsDefeat : Set where
data DeliberationEqualsPhysicalExecution : Set where

listeningDoesNotTransferAuthority : ListeningEqualsAuthorityTransfer → ⊥
listeningDoesNotTransferAuthority ()

hearingDoesNotEqualAgreement : HearingEqualsAgreement → ⊥
hearingDoesNotEqualAgreement ()

objectionDoesNotEqualDefeat : ObjectionEqualsDefeat → ⊥
objectionDoesNotEqualDefeat ()

deliberationDoesNotEqualPhysicalExecution : DeliberationEqualsPhysicalExecution → ⊥
deliberationDoesNotEqualPhysicalExecution ()

record DeliberativeMoveBoundary : Set where
  constructor deliberative-move-boundary
  field
    listenFirstClassMove : Bool
    deliberateFirstClassMove : Bool
    seriousObjectionMayReopen : Bool
    residualDisagreementMayRemainLegitimate : Bool
    authorityNotCreatedByListening : Bool

canonicalDeliberativeMoveBoundary : DeliberativeMoveBoundary
canonicalDeliberativeMoveBoundary =
  deliberative-move-boundary true true true true true
