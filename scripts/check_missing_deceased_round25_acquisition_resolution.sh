#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound25AcquisitionResolutionExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record AcquisitionResolution' "$owner"
grep -q 'h2Eligible : AcquisitionResolution → Bool' "$owner"
grep -q 'h3Eligible : AcquisitionResolution → Bool' "$owner"
grep -q 'h2Eligible r = primaryCustodyPaid r && crossPersonIdentityPaid r && sameObjectSemanticsPaid r' "$owner"
grep -q 'h3Eligible r = h2Eligible r && preEventTemporalOverlapPaid r && preEventOperationalReceiptPaid r' "$owner"
grep -q 'round25ResolutionCount = 5' "$owner"
grep -q 'round25H2EligibleCount = 0' "$owner"
grep -q 'round25H3EligibleCount = 0' "$owner"
grep -q 'primaryCustodyAloneCannotPayH2 = true' "$owner"
grep -q 'crossPersonIdentityAloneCannotPayH2 = true' "$owner"
grep -q 'sameObjectSemanticsAloneCannotPayH2 = true' "$owner"
grep -q 'h2CannotPayH3WithoutTemporalAndOperationalReceipts = true' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound25AcquisitionResolutionExact' "$agg"

echo 'Round25 acquisition-resolution static contract: OK'
