#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound70HCBTaskLevelBoundedExhaustionExact.agda"
[ -f "$OWNER" ]
grep -q "HCBTaskLevelSearchReceipt" "$OWNER"
grep -q "mccaslandTaskLevelHitLocated" "$OWNER"
grep -q "boundedSearchExhaustedForCurrentSurface" "$OWNER"
grep -q "boundedNoHitDoesNotPayUniversalNonParticipation" "$OWNER"
grep -q "derivativeRepetitionCannotKeepBranchParetoLive" "$OWNER"
grep -q "hcbBranchMayYieldUntilNewIdentityLead" "$OWNER"
grep -q "round70H2PaidCount" "$OWNER"
grep -q "round70H3PaidCount" "$OWNER"
