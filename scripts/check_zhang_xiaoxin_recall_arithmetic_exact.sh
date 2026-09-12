#!/usr/bin/env bash
set -euo pipefail
root="${1:-.}"
owner="$root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastRecallArithmeticExact.agda"
test -f "$owner"
grep -q 'eventPartitionCloses = refl' "$owner"
grep -q 'lowerRecallBracketCloses = refl' "$owner"
grep -q 'upperRecallBracketCloses = refl' "$owner"
grep -q 'reportedRecallPerMille = 777' "$owner"
grep -q 'roundedRecallDoesNotPayOperationalThreshold = false' "$owner"
echo 'Zhang Xiaoxin recall arithmetic static contract: OK'
