#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound55ResidualPaymentParetoRerunExact.agda"

[ -f "$OWNER" ]
grep -q "SchedulerState" "$OWNER"
grep -q "residualPaymentInvalidatesStaleFrontierReceipt" "$OWNER"
grep -q "admittedNarrowingTriggersParetoRerun" "$OWNER"
grep -q "contestedOrReopenedResidualTriggersParetoRerun" "$OWNER"
grep -q "blockedResidualCanDemoteTask" "$OWNER"
grep -q "siblingTaskCanEnterAfterRerun" "$OWNER"
grep -q "offFrontierRequirementRemainsRecorded" "$OWNER"
grep -q "rerunPreservesEvidenceHistory" "$OWNER"
grep -q "round55H2PaidCount" "$OWNER"
grep -q "round55H3PaidCount" "$OWNER"
