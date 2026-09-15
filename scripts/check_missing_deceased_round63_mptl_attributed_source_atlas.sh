#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound63MPTLAttributedSourceAtlasExact.agda"

[ -f "$OWNER" ]
grep -q "mptlAttributedSourceAtlas" "$OWNER"
grep -q "schulzeAchromatSource" "$OWNER"
grep -q "brandesECRSource" "$OWNER"
grep -q "chavezBPMSource" "$OWNER"
grep -q "pressBrandesAchromatProceedingsSource" "$OWNER"
grep -q "pressJaworskiDARHTDOISource" "$OWNER"
grep -q "mptlExactCarrierDOIUnresolvedIsAtlasLocal" "$OWNER"
grep -q "relatedDOICannotTransferToMPTLClaim" "$OWNER"
grep -q "bibliographicMirrorDoesNotMultiplyProof" "$OWNER"
grep -q "round63H2PaidCount" "$OWNER"
grep -q "round63H3PaidCount" "$OWNER"
