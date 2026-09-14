#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
ladder="$root/DASHI/Culture/MissingDeceasedLiteralObjectEvidenceLadderExact.agda"
round16="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound16LiteralObjectProgressExact.agda"
promotion="$root/DASHI/Culture/MissingDeceasedCommonProgrammePromotionStateExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$ladder"
test -f "$round16"
test -f "$promotion"
test -f "$agg"

grep -q 'data ObjectEvidenceClass' "$ladder"
grep -q 'personReference' "$ladder"
grep -q 'programmeObjectIdentifier' "$ladder"
grep -q 'crossPersonSameProgramme' "$ladder"
grep -q 'preEventOperationalLink' "$ladder"
grep -q 'ningArmyAgreementReceipt' "$ladder"
grep -q 'rezaMondaloyProcurementReceipt' "$ladder"
grep -q 'amyNingHistoricalReferenceReceipt' "$ladder"
grep -q 'personReferencePaysSameProgramme = false' "$ladder"
grep -q 'programmeIdentifierPaysCrossPersonLink = false' "$ladder"
grep -q 'laterProcurementPaysEarlierCommandInvolvement = false' "$ladder"
grep -q 'literalCrossPersonSameProgrammeCount = 0' "$ladder"

grep -q 'round16ScientificCohortCount = 20' "$round16"
grep -q 'round16EveryScientistTouched = true' "$round16"
grep -q 'round16H2PromotionCount = 0' "$round16"
grep -q 'round16H3PromotionCount = 0' "$round16"
grep -q 'round16SearchResidualCreatesKnownAbsence = false' "$round16"

grep -q 'currentHypothesis = Common.H1' "$promotion"
grep -q 'h0Admissible = true' "$promotion"
grep -q 'h2Paid = false' "$promotion"
grep -q 'h3Paid = false' "$promotion"
grep -q 'programmeObjectIdsIncreaseSearchPriority = true' "$promotion"
grep -q 'programmeObjectIdsIncreaseHypothesisLevel = false' "$promotion"

grep -q 'MissingDeceasedLiteralObjectEvidenceLadderExact' "$agg"
grep -q 'MissingDeceasedTwentyScientistRound16LiteralObjectProgressExact' "$agg"
grep -q 'MissingDeceasedCommonProgrammePromotionStateExact' "$agg"

echo 'Round16 literal-object acquisition static contract: OK'
