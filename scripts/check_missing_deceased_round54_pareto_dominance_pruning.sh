#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound54ParetoDominancePruningExact.agda"

[ -f "$OWNER" ]
grep -q "lowYieldExactObjectSnowball" "$OWNER"
grep -q "lowYieldSnowballEligible" "$OWNER"
grep -q "chavezDominatesLowYield" "$OWNER"
grep -q "lowYieldCannotDominateChavez" "$OWNER"
grep -q "eligibleButDominatedStaysOffCurrentParetoFrontier" "$OWNER"
grep -q "dominatedDoesNotMeanDeleted" "$OWNER"
grep -q "schedulerRerunsAfterResidualChange" "$OWNER"
grep -q "round54H2PaidCount" "$OWNER"
grep -q "round54H3PaidCount" "$OWNER"
