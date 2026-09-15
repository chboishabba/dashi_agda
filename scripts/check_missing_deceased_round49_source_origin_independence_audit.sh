#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound49SourceOriginIndependenceAuditExact.agda"

[ -f "$OWNER" ]
grep -q "ExternalClusterIndependenceStatus" "$OWNER"
grep -q "chinaClusterExternallyAssembledPaid" "$OWNER"
grep -q "chinaClusterIndependentlyAssembledPaid" "$OWNER"
grep -q "indiaTodayUsesUnderlyingChineseAndSCMPSources" "$OWNER"
grep -q "newsNationIndependenceFromIndiaTodayUnresolved" "$OWNER"
grep -q "repeatedClusterNarrativeCannotMultiplyIndependentEvidence" "$OWNER"
grep -q "externalCoverageClaimRequiresIndependenceQualification" "$OWNER"
grep -q "round49H2PaidCount" "$OWNER"
grep -q "round49H3PaidCount" "$OWNER"
