#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound24ProgrammeBridgeCandidatesExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record ProgrammeBridgeCandidate' "$owner"
grep -q 'data BridgePromotionStatus' "$owner"
grep -q 'sameObjectSemanticsPaid' "$owner"
grep -q 'crossPersonIdentityPaid' "$owner"
grep -q 'preEventTemporalOverlapPaid' "$owner"
grep -q 'sourceIdentity' "$owner"
grep -q 'sourceKind' "$owner"
grep -q 'pays' "$owner"
grep -q 'doesNotPay' "$owner"
grep -q 'ningArmyCandidate' "$owner"
grep -q 'amyNingCandidate' "$owner"
grep -q 'rezaMcCaslandCandidate' "$owner"
grep -q 'jplCandidate' "$owner"
grep -q 'nudtCandidate' "$owner"
grep -q 'round24CandidateCount = 5' "$owner"
grep -q 'round24H2PaidCount = 0' "$owner"
grep -q 'round24H3PaidCount = 0' "$owner"
grep -q 'promotionRequiresSameObjectAndCrossPersonIdentity = true' "$owner"
grep -q 'searchFailureIsNotNonexistence = true' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound24ProgrammeBridgeCandidatesExact' "$agg"

echo 'Round24 programme-bridge candidate contract: OK'
