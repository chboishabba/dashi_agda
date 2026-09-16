#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound72AmyRichardPOAMSCandidateWeldExact.agda"
[ -f "$OWNER" ]
grep -q "AmyReferentCandidateReceipt" "$OWNER"
grep -q "richardOnAmyTeamPaid" "$OWNER"
grep -q "richardNASAAuthorshipPaid" "$OWNER"
grep -q "poamsNASAReviewPublicationCarrierPaid" "$OWNER"
grep -q "candidateReferentStrengthened" "$OWNER"
grep -q "exactSamePaperIdentityPaid" "$OWNER"
grep -q "predicateIntersectionStillDoesNotPayReferentIdentity" "$OWNER"
grep -q "round72H2PaidCount" "$OWNER"
grep -q "round72H3PaidCount" "$OWNER"
