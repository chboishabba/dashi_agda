#!/usr/bin/env bash
set -euo pipefail

target='DASHI/Culture/MissingDeceasedTwentyScientistRound88NingAMCOMPrimaryAcquisitionContractExact.agda'

test -f "$target"
grep -q 'amcomCurrentFOIARoutePaid' "$target"
grep -q 'waybackByteAcquisitionAttempted' "$target"
grep -q 'toolAccessFailureDoesNotPaySourceAbsence' "$target"
grep -q 'exactRecordClassRequestRequired' "$target"
