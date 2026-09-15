#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound68HCBDOITechnicalLineageExact.agda"

[ -f "$OWNER" ]
grep -q "hcbRetrospectiveDOI" "$OWNER"
grep -q "hcbRetrospectiveAuthorCount" "$OWNER"
grep -q "hcbRetrospectiveNamesMcCaslandPaid" "$OWNER"
grep -q "hcbRetrospectivePaysMondaloyWithinHCB" "$OWNER"
grep -q "jglobalIndependentBibliographicMirrorPaid" "$OWNER"
grep -q "technicalLineageDoesNotPayManagementRole" "$OWNER"
grep -q "doiCarrierDoesNotCreateMissingAuthor" "$OWNER"
grep -q "round68H2PaidCount" "$OWNER"
grep -q "round68H3PaidCount" "$OWNER"
