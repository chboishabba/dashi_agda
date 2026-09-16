#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound75POAMSSpaceActSubagreementExact.agda"
[ -f "$OWNER" ]
grep -q "SAA8-1519855.1" "$OWNER"
grep -q "poamsFamiliarizationSubagreementPaid" "$OWNER"
grep -q "mainAgreementAndPOAMSSubagreementDistinguished" "$OWNER"
grep -q "subagreementDoesNotIdentifyAmyOrRichard" "$OWNER"
grep -q "secondaryReleaseProcessLeadCannotPromoteIdentity" "$OWNER"
grep -q "samePaperIdentityStillUnpaid" "$OWNER"
grep -q "round75H2PaidCount" "$OWNER"
grep -q "round75H3PaidCount" "$OWNER"
