#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound62MPTLAchromatPublicationWeldExact.agda"
[ -f "$OWNER" ]
grep -q "ieeeAchromatPublicationReceipt" "$OWNER"
grep -q "pressBrandesCamposSchulzeJaworskiCoauthorPaid" "$OWNER"
grep -q "formalAchromatPublicationPaid" "$OWNER"
grep -q "jGlobalBibliographicMirrorPaid" "$OWNER"
grep -q "bibliographicMirrorDoesNotCreateIndependentTechnicalObservation" "$OWNER"
grep -q "chavezStillOnlyRetainedScientistOnMPTLObjectFamily" "$OWNER"
grep -q "round62H2PaidCount" "$OWNER"
grep -q "round62H3PaidCount" "$OWNER"
