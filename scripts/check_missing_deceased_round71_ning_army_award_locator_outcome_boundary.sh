#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound71NingArmyAwardLocatorOutcomeBoundaryExact.agda"
[ -f "$OWNER" ]
grep -q "NingArmyAwardReceipt" "$OWNER"
grep -q "armyAwardLocatorPaid" "$OWNER"
grep -q "primaryBytesCustodyPaid" "$OWNER"
grep -q "authoritativeArmyFinalReportLocated" "$OWNER"
grep -q "scheduledDatesDoNotPayCompletion" "$OWNER"
grep -q "noPublicFinalReportDoesNotPayClassification" "$OWNER"
grep -q "secondaryConvergenceDoesNotReplacePrimaryCustody" "$OWNER"
grep -q "round71H2PaidCount" "$OWNER"
grep -q "round71H3PaidCount" "$OWNER"
