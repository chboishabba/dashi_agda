#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound64DOIFacilityLineageNegativeControlExact.agda"

[ -f "$OWNER" ]
grep -q "dcxStrategyDOISource" "$OWNER"
grep -q "dcxEarlierStrategyDOISource" "$OWNER"
grep -q "doiStrengthensCarrierIdentityNotClaimScope" "$OWNER"
grep -q "facilityLevelCoauthoringDoesNotPayMPTLSameObject" "$OWNER"
grep -q "mptlAuthorsMayAppearInDARHTLineageWithoutMPTLReceipt" "$OWNER"
grep -q "doiCannotBridgeObjectGranularity" "$OWNER"
grep -q "round64H2PaidCount" "$OWNER"
grep -q "round64H3PaidCount" "$OWNER"
