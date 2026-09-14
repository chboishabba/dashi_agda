#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound17PromotionDebtRoadmapExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'data PromotionStage' "$owner"
grep -q 'record PromotionDebt' "$owner"
grep -q 'round17ScientificCohortCount = 20' "$owner"
grep -q 'round17EveryScientistTouched = true' "$owner"
grep -q 'round17H2PaidCount = 0' "$owner"
grep -q 'round17H3PaidCount = 0' "$owner"
grep -q 'h1ToH2RequiresLiteralCrossPersonProgrammeReceipt = true' "$owner"
grep -q 'h2ToH3RequiresOperationalTargetingEvidence = true' "$owner"
grep -q 'temporalConcentrationCannotSkipH2 = true' "$owner"
grep -q 'scienceCoverageCannotSkipProgrammeIdentity = true' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound17PromotionDebtRoadmapExact' "$agg"

echo 'Round17 promotion-debt roadmap static contract: OK'
