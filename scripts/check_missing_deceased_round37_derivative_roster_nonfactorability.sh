#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound37DerivativeRosterNonFactorabilityExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'data ContractRoleWorld' "$owner"
grep -q 'derivativeRosterQueryDefect' "$owner"
grep -q 'derivativeRosterCannotDetermineExactRole' "$owner"
grep -q 'currentDerivativeRosterAbsenceCannotPayNonParticipation = true' "$owner"
grep -q 'syntheticCollisionDoesNotAssertHistoricalParticipation = true' "$owner"
grep -q 'round37H2PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound37DerivativeRosterNonFactorabilityExact' "$agg"

echo 'Round37 derivative-roster non-factorability static contract: OK'
