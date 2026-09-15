#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound35HCBCrossGranularityNonFactorabilityExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record HCBCrossGranularityPaidSurface' "$owner"
grep -q 'monicaExactHCBObjectRolePaid = true' "$owner"
grep -q 'mccaslandHCBProgrammeReferencePaid = true' "$owner"
grep -q 'mccaslandExactTaskRolePaid = false' "$owner"
grep -q 'crossPersonSameTaskPaid = false' "$owner"
grep -q 'hcbCrossGranularityQueryDefect' "$owner"
grep -q 'paidCrossGranularitySurfaceCannotDetermineSameTask' "$owner"
grep -q 'round35H2PaidCount = 0' "$owner"
grep -q 'round35H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound35HCBCrossGranularityNonFactorabilityExact' "$agg"

echo 'Round35 HCB cross-granularity nonfactorability static contract: OK'
