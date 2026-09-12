#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistEmbodiedTechnologyBidiExact.agda"

test -f "$owner"
grep -q 'twentyScientistEmbodiedTechnologySlots' "$owner"
grep -q 'twentyScientistEmbodiedTechnologySlotCount = 20' "$owner"
grep -q 'finiteOrStrongerScienceSlotCount = 18' "$owner"
grep -q 'identityOrAuthorshipGatedSlotCount = 2' "$owner"
grep -q 'embodiedTwentyScientistResearchPlatform' "$owner"
grep -q 'possibleCompositeUseImpliesHistoricalSystem = false' "$owner"
grep -q 'embodimentImpliesRosterCollaboration = false' "$owner"
grep -q 'finiteMechanismImpliesOperationalQualification = false' "$owner"
grep -q 'MissingDeceasedTwentyScientistEmbodiedTechnologyBidiExact' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

echo 'Twenty-scientist embodied technology BIDI static contract: OK'
