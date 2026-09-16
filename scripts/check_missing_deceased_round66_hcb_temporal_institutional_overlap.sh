#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound66HCBTemporalInstitutionalOverlapExact.agda"
[ -f "$OWNER" ]
grep -q "mccaslandAFRLCommandOverlapPaid" "$OWNER"
grep -q "hcbExactContractActiveDuringCommandPaid" "$OWNER"
grep -q "personalHCBTaskRolePaid" "$OWNER"
grep -q "mediaDirectSupervisionClaimPaid" "$OWNER"
grep -q "temporalInstitutionalOverlapDoesNotPayExactObject" "$OWNER"
grep -q "round66H2PaidCount" "$OWNER"
grep -q "round66H3PaidCount" "$OWNER"
