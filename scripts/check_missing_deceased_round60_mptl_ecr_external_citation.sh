#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound60MPTLECRExternalCitationExact.agda"

[ -f "$OWNER" ]
grep -q "mptlECRReceipt" "$OWNER"
grep -q "mptlECRPublicReleasePaid" "$OWNER"
grep -q "mptlECRExternalTechnicalCitationPaid" "$OWNER"
grep -q "externalCitationDoesNotPayPersonnelCrossing" "$OWNER"
grep -q "mptlECRAssessment" "$OWNER"
grep -q "mptlECRFeedbackRecomputes" "$OWNER"
grep -q "round60H2PaidCount" "$OWNER"
grep -q "round60H3PaidCount" "$OWNER"
