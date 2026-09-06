module DASHI.Core.DeliberativeMoveBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

-- Source calibration: Bartlett, Marshall & Marshall (2012), DOI 10.1007/s13412-012-0086-8.
-- DASHI extension only; not a universal Indigenous governance model.

data EpistemicMoveKind : Set where
  thinkMove lookMove testMove askMove listenMove deliberateMove actMove : EpistemicMoveKind

data DeliberationOutcome : Set where
  consensusReached legitimateResidualDisagreement proposalRevised moreHearingRequired : DeliberationOutcome

record SituatedParticipant : Set where
  constructor situated-participant
  field participantReference authorityReference permissionReference : String
open SituatedParticipant public

record Objection : Set where
  constructor objection
  field objector : SituatedParticipant
        objectionReference affectedInterestReference : String
        serious : Bool
open Objection public

record DeliberativeMove : Set where
  constructor deliberative-move
  field moveKind : EpistemicMoveKind
        residualReference participantReference authorityReceiptReference expectedInformationGainReference : String
open DeliberativeMove public

record ReopenOnSeriousObjection : Set where
  constructor reopen-on-serious-objection
  field objection : Objection
        seriousIsTrue : serious objection ≡ true
        reopenedResidualReference reformulationReference : String
open ReopenOnSeriousObjection public

data ListeningEqualsAuthorityTransfer : Set where
data HearingEqualsAgreement : Set where
data DeliberationEqualsPhysicalExecution : Set where

listeningDoesNotTransferAuthority : ListeningEqualsAuthorityTransfer → ⊥
listeningDoesNotTransferAuthority ()
hearingDoesNotEqualAgreement : HearingEqualsAgreement → ⊥
hearingDoesNotEqualAgreement ()
deliberationDoesNotEqualPhysicalExecution : DeliberationEqualsPhysicalExecution → ⊥
deliberationDoesNotEqualPhysicalExecution ()

record DeliberativeMoveBoundary : Set where
  constructor deliberative-move-boundary
  field listenFirstClassMove deliberateFirstClassMove seriousObjectionMayReopen residualDisagreementMayRemainLegitimate authorityNotCreatedByListening : Bool

canonicalDeliberativeMoveBoundary : DeliberativeMoveBoundary
canonicalDeliberativeMoveBoundary = deliberative-move-boundary true true true true true
