#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound56ProofCarryingSchedulerFeedbackExact.agda"

[ -f "$OWNER" ]
grep -q "AcquisitionAssessment" "$OWNER"
grep -q "AssessmentOutcome" "$OWNER"
grep -q "attributedPropositionRequiredBeforeSchedulerMutation" "$OWNER"
grep -q "frontierDeltaRequiredBeforeRerun" "$OWNER"
grep -q "affectedNeighbourhoodRequiredBeforeRerun" "$OWNER"
grep -q "admittedPaymentProducesRerunReceipt" "$OWNER"
grep -q "rejectedResultCannotPayResidual" "$OWNER"
grep -q "contestedResultCanReopenWithoutPaying" "$OWNER"
grep -q "proofCarryingRerunPreservesPriorHistory" "$OWNER"
grep -q "round56H2PaidCount" "$OWNER"
grep -q "round56H3PaidCount" "$OWNER"
