#!/usr/bin/env bash
set -euo pipefail

branch_root="${1:-.}"

required_files=(
  "DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastProducerExecutionReadinessExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistPublicProducerExecutionBidiExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistRound17ProducerExecutionProgressExact.agda"
)

for file in "${required_files[@]}"; do
  test -f "$branch_root/$file"
done

grep -q 'zhangProducerExecutionReadiness' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastProducerExecutionReadinessExact.agda"
grep -q 'producerExecutionBindingsCount = 1' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistPublicProducerExecutionBidiExact.agda"
grep -q 'round17ScientificCohortCount = 20' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound17ProducerExecutionProgressExact.agda"
grep -q 'round17EveryScientistTouched = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound17ProducerExecutionProgressExact.agda"
grep -q 'producerLocatedDoesNotMeanProducerExecuted = false' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastProducerExecutionReadinessExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound17ProducerExecutionProgressExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
grep -q 'MissingDeceasedTwentyScientistPublicProducerExecutionBidiExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

echo 'Round-17 public producer execution static contract: OK'
