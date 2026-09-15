#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound23PromotionDebtRoadmapExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'data PromotionStage' "$owner"
grep -q 'record PromotionDebt' "$owner"
grep -q 'round23ScientificCohortCount = 20' "$owner"
grep -q 'round23EveryScientistTouched = true' "$owner"
grep -q 'round23H2PaidCount = 0' "$owner"
grep -q 'round23H3PaidCount = 0' "$owner"
grep -q 'h1ToH2RequiresLiteralCrossPersonProgrammeReceipt = true' "$owner"
grep -q 'h2ToH3RequiresOperationalTargetingEvidence = true' "$owner"
grep -q 'temporalConcentrationCannotSkipH2 = true' "$owner"
grep -q 'scienceCoverageCannotSkipProgrammeIdentity = true' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound23PromotionDebtRoadmapExact' "$agg"

echo 'Round23 promotion-debt roadmap static contract: OK'
