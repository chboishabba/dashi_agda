module DASHI.Governance.OccupyMeetingPanelRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyMeetingPanelExact as Panel

oct15DurationPinned :
  Panel.durationMinutes Panel.oct15PanelRow ≡ Panel.measured 180
oct15DurationPinned = refl

oct22DurationPinned :
  Panel.durationMinutes Panel.oct22PanelRow ≡ Panel.measured 155
oct22DurationPinned = refl

oct22IncidencePinned :
  Panel.admittedIncidenceEdges Panel.oct22PanelRow ≡ Panel.measured 18
oct22IncidencePinned = refl

oct22PrepostedAgendaPinned :
  Panel.prepostedAgendaItemCount Panel.oct22PanelRow ≡ Panel.measured 10
oct22PrepostedAgendaPinned = refl

nov06NamedCountPinned :
  Panel.namedParticipantCount Panel.nov06PanelRow ≡ Panel.measured 10
nov06NamedCountPinned = refl

nov06AttendanceNotComplete :
  Panel.attendanceListClaimedComplete Panel.nov06PanelRow ≡ false
nov06AttendanceNotComplete = refl

feb19NamedCountPinned :
  Panel.namedParticipantCount Panel.feb19PanelRow ≡ Panel.measured 13
feb19NamedCountPinned = refl

feb19AgendaCountPinned :
  Panel.prepostedAgendaItemCount Panel.feb19PanelRow ≡ Panel.measured 7
feb19AgendaCountPinned = refl

feb26NamedCountPinned :
  Panel.namedParticipantCount Panel.feb26PanelRow ≡ Panel.measured 10
feb26NamedCountPinned = refl

feb26AgendaCountUnmeasured :
  Panel.prepostedAgendaItemCount Panel.feb26PanelRow ≡ Panel.unmeasured
feb26AgendaCountUnmeasured = refl

missingnessIsNotZero :
  Panel.unmeasuredIsZero Panel.canonicalMeetingPanelBoundary ≡ false
missingnessIsNotZero = refl

postedAgendaNotObservedIssueSet :
  Panel.prepostedAgendaEqualsObservedIssueSet Panel.canonicalMeetingPanelBoundary ≡ false
postedAgendaNotObservedIssueSet = refl
