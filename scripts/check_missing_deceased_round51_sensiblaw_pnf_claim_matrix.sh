#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound51SensibLawPNFClaimMatrixExact.agda"

[ -f "$OWNER" ]
grep -q "ClaimStage" "$OWNER"
grep -q "ClaimSourceMatrixRow" "$OWNER"
grep -q "ProfessionalResidual" "$OWNER"
grep -q "rezaMcCaslandHCBRow" "$OWNER"
grep -q "chineseClusterProvenanceRow" "$OWNER"
grep -q "casiasGarciaEmploymentRow" "$OWNER"
grep -q "congressionalInquiryRow" "$OWNER"
grep -q "oneSourceCannotPayAllClaimStages" "$OWNER"
grep -q "sourceAttachmentDoesNotCreateAuthority" "$OWNER"
grep -q "wrongTypeOrClassificationDoesNotDetermineDisposition" "$OWNER"
grep -q "unpaidResidualMustRemainVisible" "$OWNER"
grep -q "consumerSpecificGateCannotRewriteNativeEvidence" "$OWNER"
grep -q "round51H2PaidCount" "$OWNER"
grep -q "round51H3PaidCount" "$OWNER"
