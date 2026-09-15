#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound28AmyNASACandidateWeldExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record AmyNASAPaperCandidateWeld' "$owner"
grep -q 'nasaTM20205010911PrimaryPaid = true' "$owner"
grep -q 'nasaSAA81519855Paid = true' "$owner"
grep -q 'amyStatementNASAReviewClaimPaid = true' "$owner"
grep -q 'timelineCompatibilityPaid = true' "$owner"
grep -q 'exactReportIdentityPaid = false' "$owner"
grep -q 'teamMemberIdentityPaid = false' "$owner"
grep -q 'candidateReportNamesAmy = false' "$owner"
grep -q 'sameObjectSemanticsPaid = false' "$owner"
grep -q 'publicationAfterStatementCannotPayIdentity = true' "$owner"
grep -q 'round28H2PaidCount = 0' "$owner"
grep -q 'round28H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound28AmyNASACandidateWeldExact' "$agg"

echo 'Round28 Amy/NASA candidate-weld static contract: OK'
