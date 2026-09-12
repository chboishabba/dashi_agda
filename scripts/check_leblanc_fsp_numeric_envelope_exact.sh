#!/usr/bin/env bash
set -euo pipefail
root="${1:-.}"
owner="$root/DASHI/Physics/Nuclear/LeBlancFSPICNumericEnvelopeExact.agda"
test -f "$owner"
grep -q 'pressureSpanKPa = 600' "$owner"
grep -q 'pressureSpanCloses = refl' "$owner"
grep -q 'massFlowSpanHundredths = 45' "$owner"
grep -q 'massFlowSpanCloses = refl' "$owner"
grep -q 'temperatureIsOneSidedThreshold = true' "$owner"
grep -q 'notionalEnvelopeDoesNotPayQualification = false' "$owner"
echo 'LeBlanc FSP numeric envelope static contract: OK'
