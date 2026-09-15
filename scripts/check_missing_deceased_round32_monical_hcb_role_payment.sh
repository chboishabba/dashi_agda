#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound32MonicaHCBRolePaymentExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record MonicaHCBRoleReceipt' "$owner"
grep -q 'monicaMondaloyInventorPaid = true' "$owner"
grep -q 'monicaHCBProjectRolePaid = true' "$owner"
grep -q 'mondaloyHCBProjectIdentityPaid = true' "$owner"
grep -q 'mccaslandHCBPersonalRolePaid = false' "$owner"
grep -q 'crossPersonSameObjectPaid = false' "$owner"
grep -q 'onePersonObjectRoleCannotPayCrossPersonBridge = true' "$owner"
grep -q 'round32H2PaidCount = 0' "$owner"
grep -q 'round32H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound32MonicaHCBRolePaymentExact' "$agg"

echo 'Round32 Monica HCB role-payment static contract: OK'
