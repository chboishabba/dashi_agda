#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound34McCaslandHCBPublicReferenceExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record McCaslandHCBPublicReferenceReceipt' "$owner"
grep -q 'aiaaPanelParticipationPaid = true' "$owner"
grep -q 'personalHCBReferencePaid = true' "$owner"
grep -q 'rd180PolicyContextPaid = true' "$owner"
grep -q 'hcbTaskRolePaid = false' "$owner"
grep -q 'hcbContractRolePaid = false' "$owner"
grep -q 'mondaloyRolePaid = false' "$owner"
grep -q 'crossPersonSameObjectPaid = false' "$owner"
grep -q 'publicProgrammeReferenceCannotPayTaskRole = true' "$owner"
grep -q 'round34H2PaidCount = 0' "$owner"
grep -q 'round34H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound34McCaslandHCBPublicReferenceExact' "$agg"

echo 'Round34 McCasland HCB public-reference static contract: OK'
