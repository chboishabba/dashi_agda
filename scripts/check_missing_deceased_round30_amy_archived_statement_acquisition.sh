#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound30AmyArchivedStatementAcquisitionExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record ArchivedStatementAcquisition' "$owner"
grep -q 'archivedPostLocatorPaid = true' "$owner"
grep -q 'captureTimestampPaid = true' "$owner"
grep -q 'associatePostedScreenshotPaid = true' "$owner"
grep -q 'authenticatedAmyOriginalPaid = false' "$owner"
grep -q 'paperIdentifierPaid = false' "$owner"
grep -q 'nasaReviewReceiptPaid = false' "$owner"
grep -q 'sameObjectSemanticsPaid = false' "$owner"
grep -q 'round30H2PaidCount = 0' "$owner"
grep -q 'round30H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound30AmyArchivedStatementAcquisitionExact' "$agg"

echo 'Round30 Amy archived-statement acquisition static contract: OK'
