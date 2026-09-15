#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound73AmyEvidenceLayerBoundaryExact.agda"
[ -f "$OWNER" ]
grep -q "AmyEvidenceLayer" "$OWNER"
grep -q "archivedSelfReportDoesNotPromoteInstitutionalRecord" "$OWNER"
grep -q "journalisticRetellingDoesNotPromoteSamePaperIdentity" "$OWNER"
grep -q "publicStoryCannotRecoverEvidenceStanding" "$OWNER"
grep -q "exactReferentNeedsIdentityBearingInstitutionalBridge" "$OWNER"
grep -q "goatsBoundaryReused" "$OWNER"
grep -q "round73H2PaidCount" "$OWNER"
grep -q "round73H3PaidCount" "$OWNER"
