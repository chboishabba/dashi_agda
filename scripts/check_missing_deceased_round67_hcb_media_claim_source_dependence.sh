#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound67HCBMediaClaimSourceDependenceExact.agda"

[ -f "$OWNER" ]
grep -q "mediaClaimFamilyCount" "$OWNER"
grep -q "directFundingOrSupervisionPrimaryPaid" "$OWNER"
grep -q "afrlCommandAndPortfolioPaid" "$OWNER"
grep -q "hcbExactProgrammeActivePaid" "$OWNER"
grep -q "milestonesBookNamesMcCaslandAsCommanderPaid" "$OWNER"
grep -q "milestonesBookNamesMondaloyOrHCBPaid" "$OWNER"
grep -q "mediaRepetitionDoesNotMultiplyPrimarySupport" "$OWNER"
grep -q "commanderBudgetAuthorityDoesNotPayTaskLevelFundingDecision" "$OWNER"
grep -q "boundedPrimarySearchNoHitDoesNotPayUniversalAbsence" "$OWNER"
grep -q "round67H2PaidCount" "$OWNER"
grep -q "round67H3PaidCount" "$OWNER"
