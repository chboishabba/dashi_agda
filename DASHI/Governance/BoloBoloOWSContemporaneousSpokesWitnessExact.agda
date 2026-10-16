module DASHI.Governance.BoloBoloOWSContemporaneousSpokesWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- OWS CONTEMPORANEOUS SPOKES WITNESS ATLAS
--
-- These are independent contemporaneous People’s Library records/publications.
-- They are primary records for the Library working group or contemporaneous
-- movement publications, NOT the missing NYCGA Spokes Council minutes.
--
-- Their role is therefore bounded: they can corroborate that particular design
-- rules, orientation/reportback practices and transitional-process confusion
-- were contemporaneously recorded around the Spokes transition.  They cannot
-- substitute for the underlying Spokes minutes or identify a causal effect.
------------------------------------------------------------------------

data ContemporaneousSourceClass : Set where
  libraryWorkingGroupMinutes : ContemporaneousSourceClass
  libraryWorkingGroupPublication : ContemporaneousSourceClass

record ContemporaneousSpokesWitness : Set where
  constructor contemporaneous-spokes-witness
  field
    sourceDate : String
    sourceTitle : String
    sourceURL : String
    sourceClass : ContemporaneousSourceClass
    primaryForLibraryEvent : Bool
    primaryForSpokesMeeting : Bool
    contemporaneousWithTransition : Bool
    boundedObservation : String
    nonPromotionBoundary : String

open ContemporaneousSpokesWitness public

------------------------------------------------------------------------
-- 22 October: Library meeting minutes record a Structure Working Group guest
-- explaining the proposed Spokes architecture.  The record includes rotating
-- spokes, recall, observer access, modified consensus and the stated aim of
-- moving long operational discussion out of the GA.  This is a primary Library
-- meeting record of that presentation, not the official proposal itself.
------------------------------------------------------------------------

oct22LibraryMinutes : ContemporaneousSpokesWitness
oct22LibraryMinutes =
  contemporaneous-spokes-witness
    "2011-10-22"
    "10/22/11 Meeting Minutes"
    "https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/"
    libraryWorkingGroupMinutes
    true false true
    "records a Structure Working Group presentation describing clustered/caucus participation, a spokesperson per cluster/caucus, spoke rotation every meeting, recall if a spoke does not reflect the group, observer access, 9/10 modified consensus, and an intended reduction of long GA discussions"
    "the Library minute is not the official Spokes proposal, does not prove those rules were implemented as described, and does not identify coordination cost or causal effect"

------------------------------------------------------------------------
-- 6 November (posted 8 November): Library minutes record a Spokes orientation
-- report-back and the Library's decision to seek Operations Group status.
------------------------------------------------------------------------

nov6LibraryMinutes : ContemporaneousSpokesWitness
nov6LibraryMinutes =
  contemporaneous-spokes-witness
    "2011-11-06"
    "11/6/11 Meeting Minutes"
    "https://peopleslibrary.wordpress.com/2011/11/08/11611-meeting-minutes/"
    libraryWorkingGroupMinutes
    true false true
    "records a Spokes Council orientation report-back, discussion of Operations Group versus Movement Group status, and Library consensus to seek Operations Group status"
    "the report-back is not the underlying Spokes meeting record and does not establish the realised authority or effectiveness of the emerging council"

------------------------------------------------------------------------
-- 10 November publication about the 9 November classification meeting.
-- The author explicitly distinguishes the transitional group from both the GA
-- and a fully constituted Spokes Council, describes rule/authority confusion,
-- records Library approval as an Operations Group, and states the intended
-- rotating-spoke practice.  It is a contemporaneous movement publication, not
-- formal minutes of the 9 November Spokes meeting.
------------------------------------------------------------------------

nov10LibraryOperationsPublication : ContemporaneousSpokesWitness
nov10LibraryOperationsPublication =
  contemporaneous-spokes-witness
    "2011-11-10"
    "The Library Operations Group"
    "https://peopleslibrary.wordpress.com/2011/11/10/the-library-operations-group/"
    libraryWorkingGroupPublication
    false false true
    "describes the 9 November transitional classification body as neither GA nor yet a constituted Spokes Council, reports process/authority confusion, records Library approval as an Operations Group, and describes the intended rotating-spoke practice"
    "participant/working-group interpretation of the transitional meeting is not an official Spokes minute, a neutral audit, or a causal performance estimate"

------------------------------------------------------------------------
-- 13 November: Library minutes preserve the fact that Spokes report-backs and
-- discussion were a working-group agenda item and record a contemporaneous
-- concern about archives/transparency around what happened at Spokes.
------------------------------------------------------------------------

nov13LibraryMinutes : ContemporaneousSpokesWitness
nov13LibraryMinutes =
  contemporaneous-spokes-witness
    "2011-11-13"
    "Working Group Meeting Minutes — November 13, 2011"
    "https://peopleslibrary.wordpress.com/the-working-group/working-group-meeting-minutes/"
    libraryWorkingGroupMinutes
    true false true
    "records Spokes Council report-backs/discussion as a Library agenda item and a contemporaneous desire for stronger Archives ties concerning what happened at Spokes"
    "the Library discussion does not reconstruct the complete Spokes event, documentary completeness, or participant-level realised control"

canonicalContemporaneousSpokesWitnesses : List ContemporaneousSpokesWitness
canonicalContemporaneousSpokesWitnesses =
  oct22LibraryMinutes
  ∷ nov6LibraryMinutes
  ∷ nov10LibraryOperationsPublication
  ∷ nov13LibraryMinutes
  ∷ []

record ContemporaneousSpokesBoundary : Set where
  constructor contemporaneous-spokes-boundary
  field
    contemporaneousMovementEvidencePaid : Bool
    libraryPrimaryMeetingRecordsPaid : Bool
    rotationRecallProposalSurfacePaid : Bool
    workingGroupReportbackSurfacePaid : Bool
    transitionalAuthorityConfusionSurfacePaid : Bool
    underlyingSpokesPrimaryMinutesPaid : Bool
    libraryRecordEqualsOfficialSpokesProposal : Bool
    contemporaneousPublicationEqualsSpokesMinutes : Bool
    contemporaneousRecordsIdentifySpokesCausalEffect : Bool
    contemporaneousRecordsPayTargetBoloCostBound : Bool
    recoveredPrimarySpokesMinutesStillRequired : Bool

open ContemporaneousSpokesBoundary public

canonicalContemporaneousSpokesBoundary : ContemporaneousSpokesBoundary
canonicalContemporaneousSpokesBoundary =
  contemporaneous-spokes-boundary
    true true true true true
    false false false false false
    true

canonicalContemporaneousSpokesReceipt : GenericReceipt.GenericReceipt
canonicalContemporaneousSpokesReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS contemporaneous Spokes transition witness atlas"
    "DASHI.Governance.BoloBoloOWSContemporaneousSpokesWitnessExact"
    "canonicalContemporaneousSpokesWitnesses / canonicalContemporaneousSpokesBoundary"
    "retains contemporaneous People’s Library minutes/publications that independently record proposed rotation/recall rules, orientation/reportback, Operations Group classification and transitional authority/process confusion around the 2011 Spokes transition"
    "these sources remain primary only for their own Library events/publication context; they do not replace the missing NYCGA Spokes minutes, prove implementation fidelity, identify a causal effect, or create a target bolo cost bound"
    "agda -i . DASHI/Governance/BoloBoloOWSContemporaneousSpokesWitnessRegression.agda"
