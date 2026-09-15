#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound57FirstRealAcquisitionAssessmentExact.agda"

[ -f "$OWNER" ]
grep -q "RealAcquisitionReceipt" "$OWNER"
grep -q "chavezScorpiusOSTIReceipt" "$OWNER"
grep -q "laUR2427763ExactObjectPaid" "$OWNER"
grep -q "secondRetainedScientistOnLAUR2427763Paid" "$OWNER"
grep -q "chavezRealAcquisitionAssessment" "$OWNER"
grep -q "realAcquisitionAdmittedButFrontierUnchanged" "$OWNER"
grep -q "admittedUnchangedContinuesSearch" "$OWNER"
grep -q "realAcquisitionKnowledgeGainDoesNotPayH2" "$OWNER"
grep -q "round57H2PaidCount" "$OWNER"
grep -q "round57H3PaidCount" "$OWNER"
