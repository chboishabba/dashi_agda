#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound39HCBAttributionSnowballExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'module DASHI.Culture.MissingDeceasedTwentyScientistRound39HCBAttributionSnowballExact where' "$owner"
grep -q 'record HCBSourceRoleBoundary' "$owner"
grep -q 'sourceRoleJoinTransfersHistoricalClaim = false' "$owner"
grep -q 'sourceRoleJoinCreatesProof = false' "$owner"
grep -q 'sourceRoleJoinCreatesAuthority = false' "$owner"
grep -q 'round39H2PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound39HCBAttributionSnowballExact' "$agg"

echo 'Round39 HCB attribution snowball static contract: OK'
