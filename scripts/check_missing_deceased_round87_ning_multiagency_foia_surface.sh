#!/usr/bin/env bash
set -euo pipefail

target='DASHI/Culture/MissingDeceasedTwentyScientistRound87NingMultiAgencyFOIASurfaceExact.agda'

test -f "$target"
grep -q 'fbiACGravityRequestLogPaid' "$target"
grep -q 'dodOIGACGravityRequestLogPaid' "$target"
grep -q 'osdJSProceduralClosurePaid' "$target"
grep -q 'requestCountDoesNotEqualIndependentNoRecordsCount' "$target"
