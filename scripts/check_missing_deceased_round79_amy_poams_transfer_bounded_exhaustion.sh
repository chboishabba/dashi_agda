#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Culture/MissingDeceasedTwentyScientistRound79AmyPOAMSTransferBoundedExhaustionExact.agda"

[[ -f "$owner" ]]
grep -q 'signedSAAInstrumentLocated = false' "$owner"
grep -q 'amyInstituteTransferCarrierLocated = false' "$owner"
grep -q 'boundedTransferSearchDoesNotPayUniversalAbsence = true' "$owner"
grep -q 'derivativeIPNarrativeCannotPayTransferIdentity = true' "$owner"
grep -q 'amyBranchMayYieldUntilNewPrimaryTransferLead = true' "$owner"
grep -q 'round79H2PaidCount = 0' "$owner"
grep -q 'round79H3PaidCount = 0' "$owner"
