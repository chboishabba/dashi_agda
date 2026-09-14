#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
pareto="$root/DASHI/Culture/MissingDeceasedCommonProgrammePromotionParetoExact.agda"
round20="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound20PromotionDebtProgressExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$pareto"
test -f "$round20"
test -f "$agg"

grep -q 'data PromotionSearchClass' "$pareto"
grep -q 'record PromotionSearchCandidate' "$pareto"
grep -q 'amyNingCandidate' "$pareto"
grep -q 'rezaMcCaslandCandidate' "$pareto"
grep -q 'hicksMaiwaldCandidate' "$pareto"
grep -q 'nudtChenFengCandidate' "$pareto"
grep -q 'nudtFengZhangCandidate' "$pareto"
grep -q 'literalReferenceWithoutSameProgrammeDoesNotPayH2 = false' "$pareto"
grep -q 'institutionWithoutWorkPackageDoesNotPayH2 = false' "$pareto"
grep -q 'sameProgrammeWithoutOperationalActionDoesNotPayH3 = false' "$pareto"
grep -q 'currentH2PromotionCount = 0' "$pareto"
grep -q 'currentH3PromotionCount = 0' "$pareto"

grep -q 'round20ScientificCohortCount = 20' "$round20"
grep -q 'round20EveryScientistTouched = true' "$round20"
grep -q 'round20H2PromotionCount = 0' "$round20"
grep -q 'round20H3PromotionCount = 0' "$round20"
grep -q 'round20SearchResidualCreatesKnownAbsence = false' "$round20"

grep -q 'MissingDeceasedCommonProgrammePromotionParetoExact' "$agg"
grep -q 'MissingDeceasedTwentyScientistRound20PromotionDebtProgressExact' "$agg"

echo 'Round20 promotion-debt Pareto static contract: OK'
