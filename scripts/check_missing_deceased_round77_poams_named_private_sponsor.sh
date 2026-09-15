#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound77POAMSNamedPrivateSponsorExact.agda"
[ -f "$OWNER" ]
grep -q "poamsNamedPrivateSponsorPaid" "$OWNER"
grep -q "chrisMilamRequestedAndFundedEffortPaid" "$OWNER"
grep -q "amyOrInstituteNamedOnExactPOAMSInstitutionalCarrierPaid" "$OWNER"
grep -q "privateSponsorIdentityDoesNotPayAmyBridge" "$OWNER"
grep -q "round77H2PaidCount" "$OWNER"
grep -q "round77H3PaidCount" "$OWNER"
