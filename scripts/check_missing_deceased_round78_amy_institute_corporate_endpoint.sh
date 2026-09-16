#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Culture/MissingDeceasedTwentyScientistRound78AmyInstituteCorporateEndpointExact.agda"

[[ -f "$owner" ]]
grep -q 'amyInstituteCorporateIdentityPaid = true' "$owner"
grep -q 'secFormDPrimaryCarrierPaid = true' "$owner"
grep -q 'nasaPOAMSTransferBridgePaid = false' "$owner"
grep -q 'corporateIdentityDoesNotPayNASAResearchParticipation = true' "$owner"
grep -q 'round78H2PaidCount = 0' "$owner"
grep -q 'round78H3PaidCount = 0' "$owner"
