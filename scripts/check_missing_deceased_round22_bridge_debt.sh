#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
bridge="$root/DASHI/Culture/MissingDeceasedCommonProgrammeBridgeDebtExact.agda"
round22="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound22BridgeDebtProgressExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$bridge"
test -f "$round22"
test -f "$agg"

grep -q 'data BridgePaymentClass' "$bridge"
grep -q 'record BridgeDebtReceipt' "$bridge"
grep -q 'ningArmyBridgeDebt' "$bridge"
grep -q 'amyNingBridgeDebt' "$bridge"
grep -q 'rezaMcCaslandBridgeDebt' "$bridge"
grep -q 'jplBridgeDebt' "$bridge"
grep -q 'nudtBridgeDebt' "$bridge"
grep -q 'objectIdentifierPaysSecondRetainedPerson = false' "$bridge"
grep -q 'historicalReferencePaysSharedProgramme = false' "$bridge"
grep -q 'commandAuthorityPaysSpecificProgrammeRole = false' "$bridge"
grep -q 'laterProcurementPaysEarlierPersonalParticipation = false' "$bridge"
grep -q 'h2RequiresLiteralSameObjectRoleReceipt = true' "$bridge"
grep -q 'h3RequiresPreEventOperationalReceipt = true' "$bridge"

grep -q 'round22ScientificCohortCount = 20' "$round22"
grep -q 'round22EveryScientistTouched = true' "$round22"
grep -q 'round22H2PromotionCount = 0' "$round22"
grep -q 'round22H3PromotionCount = 0' "$round22"
grep -q 'round22SearchResidualCreatesKnownAbsence = false' "$round22"

grep -q 'MissingDeceasedCommonProgrammeBridgeDebtExact' "$agg"
grep -q 'MissingDeceasedTwentyScientistRound22BridgeDebtProgressExact' "$agg"

echo 'Round22 bridge-debt static contract: OK'
