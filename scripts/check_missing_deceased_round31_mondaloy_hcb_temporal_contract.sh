#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound31MondaloyHCBTemporalContractExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record HCBTemporalContractReceipt' "$owner"
grep -q 'hcbContractIdentifierPaid = true' "$owner"
grep -q 'aerojetPrimeContractorPaid = true' "$owner"
grep -q 'mondaloyOnFY12HCBRoadmapPaid = true' "$owner"
grep -q 'materialsSupportIncludesAFRLRXAerojetPaid = true' "$owner"
grep -q 'mccaslandCommandTemporalOverlapPaid = true' "$owner"
grep -q 'mccaslandPersonalHCBRolePaid = false' "$owner"
grep -q 'jacintoOnHCBContractPaid = false' "$owner"
grep -q 'sameObjectCrossPersonReceiptPaid = false' "$owner"
grep -q 'contemporaneousProgrammeCannotPayPersonalRole = true' "$owner"
grep -q 'round31H2PaidCount = 0' "$owner"
grep -q 'round31H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound31MondaloyHCBTemporalContractExact' "$agg"

echo 'Round31 Mondaloy/HCB temporal-contract static contract: OK'
