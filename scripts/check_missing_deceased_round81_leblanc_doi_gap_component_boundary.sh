#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Culture/MissingDeceasedTwentyScientistRound81LeBlancDOIGapComponentBoundaryExact.agda"

test -f "$owner"
grep -q '10.13182/NPICHMIT25-46370' "$owner"
grep -q 'programmeGapCarrierPaid = true' "$owner"
grep -q 'sameWBSComponentCarrierPaid = true' "$owner"
grep -q 'sameWBSDoesNotPaySameComponentRole = true' "$owner"
grep -q 'secondRetainedScientistPaid = false' "$owner"
grep -q 'h2Paid = false' "$owner"
grep -q 'h3Paid = false' "$owner"
