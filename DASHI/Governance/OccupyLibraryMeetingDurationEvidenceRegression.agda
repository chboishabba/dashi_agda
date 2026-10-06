module DASHI.Governance.OccupyLibraryMeetingDurationEvidenceRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyLibraryMeetingDurationEvidenceExact as Duration

oct15DurationPinned :
  Duration.durationMinutes Duration.oct15FirstFormalMeeting ≡ 180
oct15DurationPinned = refl

oct22DurationPinned :
  Duration.durationMinutes Duration.oct22Meeting ≡ 155
oct22DurationPinned = refl

oct22ClockArithmeticPinned :
  Duration.startMinuteOfDay Duration.oct22Meeting
  + Duration.durationMinutes Duration.oct22Meeting
  ≡ Duration.endMinuteOfDay Duration.oct22Meeting
oct22ClockArithmeticPinned = refl

oct22TimekeepingTargetPinned :
  Duration.agendaTimeTargetMinutes Duration.oct22TimekeepingRule ≡ 5
oct22TimekeepingTargetPinned = refl

durationDoesNotEqualBurden :
  Duration.durationEqualsCoordinationBurden Duration.canonicalMeetingDurationBoundary ≡ false
durationDoesNotEqualBurden = refl

proceduralTargetDoesNotDescribeActualPerItemTime :
  Duration.timekeepingTargetEqualsObservedPerItemDuration Duration.canonicalMeetingDurationBoundary ≡ false
proceduralTargetDoesNotDescribeActualPerItemTime = refl
