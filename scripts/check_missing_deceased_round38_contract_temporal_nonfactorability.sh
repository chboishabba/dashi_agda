#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound38ContractTemporalNonFactorabilityExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'module DASHI.Culture.MissingDeceasedTwentyScientistRound38ContractTemporalNonFactorabilityExact where' "$owner"
grep -q 'laterContractPersistenceCannotDetermineEarlierPersonalRole' "$owner"
grep -q 'laterDerivativeLineageCannotPayEarlierRole = true' "$owner"
grep -q 'syntheticCollisionDoesNotAssertHistoricalRole = true' "$owner"
grep -q 'round38H2PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound38ContractTemporalNonFactorabilityExact' "$agg"

echo 'Round38 contract-temporal non-factorability static contract: OK'
