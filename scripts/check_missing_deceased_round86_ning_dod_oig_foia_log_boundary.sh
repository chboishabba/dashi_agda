#!/usr/bin/env bash
set -euo pipefail

target='DASHI/Culture/MissingDeceasedTwentyScientistRound86NingDODOIGFOIALogBoundaryExact.agda'

test -f "$target"
grep -q 'dodOIGRequestLogPaid' "$target"
grep -q 'sameDayClosurePaid' "$target"
grep -q 'closureDispositionUnderidentified' "$target"
grep -q 'sameDayClosureDoesNotPayNoRecords' "$target"
