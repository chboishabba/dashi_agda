module DASHI.Governance.OccupyMeetingPanelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- SOURCE-EXPLICIT MEETING PANEL.
--
-- Each coordinate is admitted only where the inspected People's Library
-- archive explicitly pays it.  Missing fields remain `unmeasured`; absence of
-- a source coordinate is never silently rewritten as zero.
--
-- Provenance split:
--   * named attendees / posted agenda counts / start-end times are primary
--     archival observations;
--   * minute conversion, finite counts and row assembly are DASHI coding;
--   * this panel is not attributed to OWS participants as their own ontology.
------------------------------------------------------------------------

data OptionalNat : Set where
  unmeasured : OptionalNat
  measured : Nat → OptionalNat

record MeetingPanelRow : Set where
  constructor meetingPanelRow
  field
    meetingLabel : String
    sourceAnchor : String
    admittedIncidenceEdges : OptionalNat
    namedParticipantCount : OptionalNat
    prepostedAgendaItemCount : OptionalNat
    durationMinutes : OptionalNat
    tabledAgendaItemCount : OptionalNat
    explicitDecisionCount : OptionalNat
    attendanceListClaimedComplete : Bool
    agendaListClaimedComplete : Bool
    sourceCompletenessAudited : Bool

open MeetingPanelRow public

oct15URL : String
oct15URL = "https://peopleslibrary.wordpress.com/2011/10/16/library-working-group-meets/"

oct22URL : String
oct22URL = "https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/"

minutesIndexURL : String
minutesIndexURL = "https://peopleslibrary.wordpress.com/the-working-group/working-group-meeting-minutes/"

feb19URL : String
feb19URL = "https://peopleslibrary.wordpress.com/2012/02/20/"

feb26URL : String
feb26URL = "https://peopleslibrary.wordpress.com/2012/02/28/working-group-meeting-minutes-26-february-2012/"

------------------------------------------------------------------------
-- Development rows.
------------------------------------------------------------------------

oct15PanelRow : MeetingPanelRow
oct15PanelRow =
  meetingPanelRow
    "People's Library first formal working-group meeting, 2011-10-15"
    oct15URL
    unmeasured
    unmeasured
    unmeasured
    (measured 180)
    unmeasured
    unmeasured
    false
    false
    false

oct22PanelRow : MeetingPanelRow
oct22PanelRow =
  meetingPanelRow
    "People's Library working-group meeting, 2011-10-22"
    oct22URL
    (measured 18)
    unmeasured
    (measured 10)
    (measured 155)
    unmeasured
    unmeasured
    false
    false
    false

-- The 6 November record explicitly lists ten names and includes the caveat
-- "sorry if I missed anybody".  We therefore retain the observed named count
-- while explicitly refusing a completeness claim.
nov06PanelRow : MeetingPanelRow
nov06PanelRow =
  meetingPanelRow
    "People's Library working-group meeting, 2011-11-06"
    minutesIndexURL
    unmeasured
    (measured 10)
    unmeasured
    unmeasured
    unmeasured
    unmeasured
    false
    false
    false

nov28PanelRow : MeetingPanelRow
nov28PanelRow =
  meetingPanelRow
    "People's Library working-group meeting, 2011-11-28"
    minutesIndexURL
    (measured 7)
    (measured 19)
    (measured 5)
    unmeasured
    unmeasured
    unmeasured
    false
    false
    false

dec04PanelRow : MeetingPanelRow
dec04PanelRow =
  meetingPanelRow
    "People's Library working-group meeting, 2011-12-04"
    minutesIndexURL
    unmeasured
    unmeasured
    unmeasured
    unmeasured
    (measured 10)
    unmeasured
    false
    false
    false

-- 19 February explicitly lists thirteen names and presents seven distinct
-- agenda-topic blocks after the `Agenda:` heading.  This count is a source-
-- document structural count, not a claim that seven issues exhaust everything
-- discussed in the meeting.
feb19PanelRow : MeetingPanelRow
feb19PanelRow =
  meetingPanelRow
    "People's Library working-group meeting, 2012-02-19"
    feb19URL
    unmeasured
    (measured 13)
    (measured 7)
    unmeasured
    unmeasured
    unmeasured
    false
    false
    false

-- 26 February explicitly lists ten named attendees.  The page is organized as
-- reportbacks/announcements rather than a bounded agenda list, so no agenda
-- count is inferred.
feb26PanelRow : MeetingPanelRow
feb26PanelRow =
  meetingPanelRow
    "People's Library working-group meeting, 2012-02-26"
    feb26URL
    unmeasured
    (measured 10)
    unmeasured
    unmeasured
    unmeasured
    unmeasured
    false
    false
    false

canonicalDevelopmentPanel : List MeetingPanelRow
canonicalDevelopmentPanel =
  oct15PanelRow
  ∷ oct22PanelRow
  ∷ nov06PanelRow
  ∷ nov28PanelRow
  ∷ dec04PanelRow
  ∷ feb19PanelRow
  ∷ feb26PanelRow
  ∷ []

------------------------------------------------------------------------
-- Promotion / attribution firewall.
------------------------------------------------------------------------

record MeetingPanelBoundary : Set where
  constructor meetingPanelBoundary
  field
    unmeasuredIsZero : Bool
    namedCountImpliesCompleteAttendance : Bool
    prepostedAgendaEqualsObservedIssueSet : Bool
    postedAgendaCountIsCoordinationBurden : Bool
    durationIsCoordinationBurden : Bool
    panelRowsAreRandomSample : Bool
    panelAssemblyIsParticipantAuthoredFormalism : Bool
    sourceCompletenessAlreadyAudited : Bool

open MeetingPanelBoundary public

canonicalMeetingPanelBoundary : MeetingPanelBoundary
canonicalMeetingPanelBoundary =
  meetingPanelBoundary
    false
    false
    false
    false
    false
    false
    false
    false

canonicalOccupyMeetingPanelReceipt : GenericReceipt.GenericReceipt
canonicalOccupyMeetingPanelReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "source-explicit Occupy People's Library meeting panel"
    "DASHI.Governance.OccupyMeetingPanelExact"
    "canonicalMeetingPanelBoundary"
    "assembles only source-paid meeting coordinates, including 180- and 155-minute durations, the 18-edge 22-Oct incidence specimen, named-attendee counts for 6-Nov/28-Nov/19-Feb/26-Feb, bounded posted-agenda counts where structurally explicit, and ten tabled items on 4-Dec"
    "missing coordinates remain unmeasured rather than zero; named lists are not assumed complete, posted agenda items are not equated with the observed issue set, and panel assembly creates neither a random sample nor an empirical coordination-cost law"
    "agda -i . DASHI/Governance/OccupyMeetingPanelRegression.agda"
