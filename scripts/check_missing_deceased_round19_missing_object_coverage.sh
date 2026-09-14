#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
astronomy="$root/DASHI/Culture/MissingDeceasedAstronomicalSurveyPlatformBidiExact.agda"
planetary="$root/DASHI/Culture/MissingDeceasedPlanetarySmallBodyObservatoryBidiExact.agda"
decision="$root/DASHI/Culture/MissingDeceasedDecisionSupportResearchPlatformBidiExact.agda"
round19="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound19MissingObjectCoverageExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$astronomy"
test -f "$planetary"
test -f "$decision"
test -f "$round19"
test -f "$agg"

grep -q 'astronomicalSurveyObject' "$astronomy"
grep -q 'grillmairDirectFit = true' "$astronomy"
grep -q 'historicalParticipationPaid = false' "$astronomy"

grep -q 'planetarySmallBodyObservatoryObject' "$planetary"
grep -q 'hicksDirectFit = true' "$planetary"
grep -q 'historicalParticipationPaid = false' "$planetary"

grep -q 'decisionSupportResearchPlatformObject' "$decision"
grep -q 'fengDirectFit = true' "$decision"
grep -q 'historicalParticipationPaid = false' "$decision"

grep -q 'round19ScientificCohortCount = 20' "$round19"
grep -q 'round19EveryScientistTouched = true' "$round19"
grep -q 'round19NoFitCount = 0' "$round19"
grep -q 'round19H2PromotionCount = 0' "$round19"
grep -q 'round19H3PromotionCount = 0' "$round19"
grep -q 'round19ObjectCoverageDoesNotPayHistoricalLink = false' "$round19"

grep -q 'MissingDeceasedAstronomicalSurveyPlatformBidiExact' "$agg"
grep -q 'MissingDeceasedPlanetarySmallBodyObservatoryBidiExact' "$agg"
grep -q 'MissingDeceasedDecisionSupportResearchPlatformBidiExact' "$agg"
grep -q 'MissingDeceasedTwentyScientistRound19MissingObjectCoverageExact' "$agg"

echo 'Round19 missing-object coverage static contract: OK'
