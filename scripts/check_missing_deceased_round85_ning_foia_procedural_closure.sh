#!/usr/bin/env bash
set -euo pipefail

target='DASHI/Culture/MissingDeceasedTwentyScientistRound85NingFOIAProceduralClosureExact.agda'

test -f "$target"
grep -q 'foiaAdministrativeClosurePaid' "$target"
grep -q 'foiaClosureDoesNotPayCompletedRecordsSearch' "$target"
grep -q 'foiaClosureDoesNotPayNoRecordsExist' "$target"
grep -q 'foiaClosureDoesNotPayConcealment' "$target"
