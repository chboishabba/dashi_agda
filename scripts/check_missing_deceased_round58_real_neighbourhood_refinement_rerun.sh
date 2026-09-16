#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound58RealNeighbourhoodRefinementRerunExact.agda"

[ -f "$OWNER" ]
grep -q "scorpiusWorkshopProceedingsReceipt" "$OWNER"
grep -q "namedScorpiusPresenterPaid" "$OWNER"
grep -q "namedDARHTMPTLPresenterPaid" "$OWNER"
grep -q "jointLabDevelopmentSurfacePaid" "$OWNER"
grep -q "secondRetainedScientistFromWorkshopPaid" "$OWNER"
grep -q "realNeighbourhoodNarrowingAssessment" "$OWNER"
grep -q "realNarrowingRecomputesFrontier" "$OWNER"
grep -q "workshopRegistrantCountDoesNotPayAttendanceIdentity" "$OWNER"
grep -q "round58H2PaidCount" "$OWNER"
grep -q "round58H3PaidCount" "$OWNER"
