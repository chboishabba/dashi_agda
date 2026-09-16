#!/usr/bin/env bash
set -euo pipefail
OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound65MPTLRetainedNameSweepExact.agda"
[ -f "$OWNER" ]
grep -q "retainedNameSweepCount" "$OWNER"
grep -q "mptlSecondRetainedPersonLocated" "$OWNER"
grep -q "boundedNoCrossingDoesNotProveUniversalAbsence" "$OWNER"
grep -q "mptlBranchShouldYieldAfterBoundedSweep" "$OWNER"
grep -q "round65H2PaidCount" "$OWNER"
grep -q "round65H3PaidCount" "$OWNER"
