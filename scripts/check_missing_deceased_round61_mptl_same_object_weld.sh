#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound61MPTLSameObjectWeldExact.agda"
[ -f "$OWNER" ]
grep -q "ipmhvcMPTLPosterReceipt" "$OWNER"
grep -q "brandesSchulzePressSameNamedMPTLObjectPaid" "$OWNER"
grep -q "pressToSchulzeBrandesGapClosed" "$OWNER"
grep -q "chavezMPTLObjectPaid" "$OWNER"
grep -q "secondRetainedScientistOnMPTLPaid" "$OWNER"
grep -q "sameNamedMPTLObjectDoesNotPaySecondRetainedPerson" "$OWNER"
grep -q "round61H2PaidCount" "$OWNER"
grep -q "round61H3PaidCount" "$OWNER"
