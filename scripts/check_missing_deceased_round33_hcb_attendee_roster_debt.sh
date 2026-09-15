#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound33HCBAttendeeRosterDebtExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record IdentityBearingAcquisitionDebt' "$owner"
grep -q 'industryDayIdentityPaid = true' "$owner"
grep -q 'attendeeNamesWereCollectedPaid = true' "$owner"
grep -q 'attendeeOrganisationWasCollectedPaid = true' "$owner"
grep -q 'restrictedTechnicalBriefingPaid = true' "$owner"
grep -q 'publicAttendeeRosterPaid = false' "$owner"
grep -q 'mccaslandAttendancePaid = false' "$owner"
grep -q 'monicaAttendancePaid = false' "$owner"
grep -q 'restrictedMeetingCannotPayLaterTargeting = true' "$owner"
grep -q 'round33H2PaidCount = 0' "$owner"
grep -q 'round33H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound33HCBAttendeeRosterDebtExact' "$agg"

echo 'Round33 HCB attendee-roster debt static contract: OK'
