#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound48AntiEchoChamberMethodologyExact.agda"

[ -f "$OWNER" ]
grep -q "SourceIndependenceClass" "$OWNER"
grep -q "sourceCountDoesNotEqualIndependentEvidenceCount" "$OWNER"
grep -q "counterSourceSearchRequired" "$OWNER"
grep -q "agreementAcrossDependentCopiesDoesNotMultiplyEvidence" "$OWNER"
grep -q "disagreementMustRemainVisible" "$OWNER"
grep -q "provenanceMustSurviveNarrativeProjection" "$OWNER"
grep -q "absenceOutsideCoveredSearchRemainsUnresolved" "$OWNER"
grep -q "antiPanopticonBoundaryAnchor" "$OWNER"
grep -q "analysisOfCompetingHypothesesAttributed" "$OWNER"
grep -q "lateralReadingAttributed" "$OWNER"
grep -q "bellingcatValidationAttributed" "$OWNER"
grep -q "adversarialCollaborationAttributed" "$OWNER"
grep -q "antiEchoChamberDoesNotCreateSurveillanceAuthority" "$OWNER"
grep -q "round48H2PaidCount" "$OWNER"
grep -q "round48H3PaidCount" "$OWNER"
