#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound59MPTLAchromatAcquisitionExact.agda"

[ -f "$OWNER" ]
grep -q "mptlAchromatReceipt" "$OWNER"
grep -q "mptlExactObjectPaid" "$OWNER"
grep -q "mptlSecondRetainedPersonPaid" "$OWNER"
grep -q "mptlMagnetProducerNarrowed" "$OWNER"
grep -q "mptlAssessment" "$OWNER"
grep -q "mptlFeedbackRecomputes" "$OWNER"
grep -q "mptlNoCrossingDoesNotProveNoCrossingAnywhere" "$OWNER"
grep -q "round59H2PaidCount" "$OWNER"
grep -q "round59H3PaidCount" "$OWNER"
