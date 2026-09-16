#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Culture/MissingDeceasedTwentyScientistRound80LeBlancWBSComponentNeighbourhoodExact.agda"

[[ -f "$owner" ]]
grep -q 'sameWBSExactKeyPaid = true' "$owner"
grep -q 'thinFilmSensorNeighbourhoodPaid = true' "$owner"
grep -q 'sandiaRadiationTestingNeighbourhoodPaid = true' "$owner"
grep -q 'secondRetainedScientistOnWBSCarrierPaid = false' "$owner"
grep -q 'sameWBSDoesNotImplySameComponentRole = true' "$owner"
grep -q 'round80H2PaidCount = 0' "$owner"
grep -q 'round80H3PaidCount = 0' "$owner"
