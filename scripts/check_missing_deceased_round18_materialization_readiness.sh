#!/usr/bin/env bash
set -euo pipefail
branch_root="${1:-.}"
required_files=(
  "DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastMaterializationExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistMaterializationBidiExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistRound18MaterializationProgressExact.agda"
)
for f in "${required_files[@]}"; do test -f "$branch_root/$f"; done

grep -q 'payloadDownloadedByDASHI = false' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastMaterializationExact.agda"
grep -q 'payloadHashesCheckedByDASHI = false' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastMaterializationExact.agda"
grep -q 'payloadParsedByDASHI = false' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastMaterializationExact.agda"
grep -q 'materializationBindingsCount = 1' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistMaterializationBidiExact.agda"
grep -q 'round18ScientificCohortCount = 20' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound18MaterializationProgressExact.agda"
grep -q 'round18EveryScientistTouched = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound18MaterializationProgressExact.agda"
grep -q 'materializationDoesNotPayExecution = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound18MaterializationProgressExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound18MaterializationProgressExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
grep -q 'MissingDeceasedTwentyScientistMaterializationBidiExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

echo 'Round-18 materialization readiness static contract: OK'
