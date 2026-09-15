#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Culture/MissingDeceasedTwentyScientistRound43NarrativeEvidenceStrataExact.agda"

test -f "$owner"
grep -q 'directEvidenceNarrative' "$owner"
grep -q 'boundedInferenceNarrative' "$owner"
grep -q 'unsupportedNarrative' "$owner"
grep -q 'round43H2PaidCount' "$owner"
grep -q 'narrativeCannotSkipPromotionGate' "$owner"
