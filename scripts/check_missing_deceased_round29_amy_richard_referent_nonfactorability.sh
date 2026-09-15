#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound29AmyRichardReferentNonFactorabilityExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'richardTeamMembershipPaid = true' "$owner"
grep -q 'richardRetiredNASAIdentityPaid = true' "$owner"
grep -q 'richardNASAReportAuthorshipPaid = true' "$owner"
grep -q 'candidatePredicateIntersectionPaid = true' "$owner"
grep -q 'unnamedReferentIdentityPaid = false' "$owner"
grep -q 'sameObjectSemanticsPaid = false' "$owner"
grep -q 'referentIdentityQueryDefect' "$owner"
grep -q 'predicateMatchCannotDetermineUnnamedReferent' "$owner"
grep -q 'round29H2PaidCount = 0' "$owner"
grep -q 'round29H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound29AmyRichardReferentNonFactorabilityExact' "$agg"

echo 'Round29 Amy/Richard referent nonfactorability static contract: OK'
