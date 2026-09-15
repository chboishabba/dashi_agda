#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound76POAMSFundingIdentifierWeldExact.agda"
[ -f "$OWNER" ]
grep -q "MSFC-RMB-QUANTUM-SAA8-1519855-1" "$OWNER"
grep -q "SAA8-1519855.1" "$OWNER"
grep -q "fundingIdentifierAgreementFamilyWeldPaid" "$OWNER"
grep -q "formatNormalizationDoesNotPayInternalRevisionIdentity" "$OWNER"
grep -q "tmInstitutionalObjectStrengthened" "$OWNER"
grep -q "amyInstituteIdentityStillUnpaid" "$OWNER"
grep -q "round76H2PaidCount" "$OWNER"
grep -q "round76H3PaidCount" "$OWNER"
