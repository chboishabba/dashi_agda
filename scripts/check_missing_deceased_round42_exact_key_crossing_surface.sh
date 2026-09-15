#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Culture/MissingDeceasedTwentyScientistRound42ExactKeyCrossingSurfaceExact.agda"

test -f "$owner"
grep -q 'round42SearchedExactKeyCount' "$owner"
grep -q 'searchedSurfaceNoCrossingCannotPayUniversalAbsence' "$owner"
grep -q 'round42H2PaidCount' "$owner"
grep -q 'round42NarrativeBoundary' "$owner"
