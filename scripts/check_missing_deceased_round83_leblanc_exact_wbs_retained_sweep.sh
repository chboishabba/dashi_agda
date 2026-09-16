#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Culture/MissingDeceasedTwentyScientistRound83LeBlancExactWBSRetainedSweepExact.agda"

test -f "$owner"
grep -q 'exactWBS = "658133.04.01.22.01.06"' "$owner"
grep -q 'leblancRetainedHitPaid = true' "$owner"
grep -q 'secondRetainedHitLocated = false' "$owner"
grep -q 'boundedNoHitDoesNotPayUniversalAbsence = true' "$owner"
grep -q 'branchMayYieldUntilNewExactLead = true' "$owner"
grep -q 'h2Paid = false' "$owner"
grep -q 'h3Paid = false' "$owner"
