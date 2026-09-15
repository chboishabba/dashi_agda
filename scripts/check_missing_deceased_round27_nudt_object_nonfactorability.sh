#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound27NUDTObjectNonFactorabilityExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record NUDTObjectReceipt' "$owner"
grep -q 'chenObjectPaid = true' "$owner"
grep -q 'fengObjectPaid = true' "$owner"
grep -q 'zhangObjectPaid = true' "$owner"
grep -q 'chenFengSharedTaskPaid = false' "$owner"
grep -q 'chenZhangSharedTaskPaid = false' "$owner"
grep -q 'fengZhangSharedTaskPaid = false' "$owner"
grep -q 'nudtInstitutionQueryDefect' "$owner"
grep -q 'institutionOnlyCannotDetermineExactSharedTask' "$owner"
grep -q 'round27H2PaidCount = 0' "$owner"
grep -q 'round27H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound27NUDTObjectNonFactorabilityExact' "$agg"

echo 'Round27 NUDT object nonfactorability static contract: OK'
