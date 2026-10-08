module DASHI.Governance.OccupyLibraryMeetingDurationEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- PRIMARY ARCHIVAL MEETING-DURATION EVIDENCE.
--
-- Source 1: People's Library post of 16 October 2011 describing the first
-- formal Library Working Group meeting held the preceding Saturday.  It says
-- the group used the General Assembly process and spent three hours discussing
-- the posted agenda.
--
-- Source 2: People's Library minutes for 22 October 2011.  The minutes record
-- a 13:00 start and a 15:35 end, and separately record a five-minute-per-agenda-
-- item timekeeping rule.
--
-- Attribution boundary:
--   * duration observations are primary archival observations;
--   * conversion of three hours -> 180 minutes and 13:00..15:35 -> 155 minutes
--     is DASHI arithmetic/coding;
--   * a procedural target is not promoted to actual observed per-item duration;
--   * meeting duration is not definitionally coordination burden.
------------------------------------------------------------------------

record MeetingDurationObservation : Set where
  constructor meetingDurationObservation
  field
    meetingLabel : String
    sourceURL : String
    sourceDurationAnchor : String
    startMinuteOfDay : Nat
    endMinuteOfDay : Nat
    durationMinutes : Nat
    sourceStatesDurationDirectly : Bool

open MeetingDurationObservation public

oct15FirstFormalMeeting : MeetingDurationObservation
oct15FirstFormalMeeting =
  meetingDurationObservation
    "People's Library first formal working-group meeting, 2011-10-15"
    "https://peopleslibrary.wordpress.com/2011/10/16/library-working-group-meets/"
    "archive post states that the meeting used the General Assembly process and spent three hours discussing agenda items"
    0
    0
    180
    true

oct22Meeting : MeetingDurationObservation
oct22Meeting =
  meetingDurationObservation
    "People's Library Library Working Group meeting, 2011-10-22"
    "https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/"
    "minutes record 13:00 start and 15:35 end"
    780
    935
    155
    false

oct22ClockArithmetic :
  startMinuteOfDay oct22Meeting + durationMinutes oct22Meeting
  ≡ endMinuteOfDay oct22Meeting
oct22ClockArithmetic = refl

record AgendaTimekeepingObservation : Set where
  constructor agendaTimekeepingObservation
  field
    meetingLabel : String
    sourceURL : String
    sourceAnchor : String
    agendaTimeTargetMinutes : Nat

open AgendaTimekeepingObservation public

oct22TimekeepingRule : AgendaTimekeepingObservation
oct22TimekeepingRule =
  agendaTimekeepingObservation
    "People's Library Library Working Group meeting, 2011-10-22"
    "https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/"
    "minutes state: Timekeeping: 5 minutes each agenda item"
    5

record MeetingDurationEvidenceBoundary : Set where
  constructor meetingDurationEvidenceBoundary
  field
    archivePaysOct15ThreeHourDuration : Bool
    archivePaysOct22StartEndTimes : Bool
    archivePaysOct22FiveMinuteAgendaTarget : Bool
    dashiArithmeticPaysOct22Duration155 : Bool

    durationEqualsCoordinationBurden : Bool
    timekeepingTargetEqualsObservedPerItemDuration : Bool
    oct15DurationIdentifiesCauseOfLength : Bool
    oct22DurationIdentifiesConsensusCost : Bool
    twoMeasuredDurationsPayScalingLaw : Bool

open MeetingDurationEvidenceBoundary public

canonicalMeetingDurationBoundary : MeetingDurationEvidenceBoundary
canonicalMeetingDurationBoundary =
  meetingDurationEvidenceBoundary
    true
    true
    true
    true
    false
    false
    false
    false
    false

canonicalMeetingDurationEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalMeetingDurationEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "People's Library archival meeting-duration evidence"
    "DASHI.Governance.OccupyLibraryMeetingDurationEvidenceExact"
    "canonicalMeetingDurationBoundary"
    "retains a source-stated three-hour duration for the first formal Library Working Group meeting and source-recorded 13:00-to-15:35 clock bounds for 22 October 2011, with DASHI arithmetic yielding 155 minutes; also retains the source-recorded five-minute agenda-item timekeeping target"
    "duration is not promoted to coordination burden, procedural time target is not observed per-item duration, and two measured meetings do not identify a consensus-cost or scaling law"
    "agda -i . DASHI/Governance/OccupyLibraryMeetingDurationEvidenceRegression.agda"
