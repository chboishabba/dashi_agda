#!/usr/bin/env bash
set -euo pipefail
branch_root="${1:-.}"
required_files=(
  "DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastPublicProducerExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistRound16PublicProducerProgressExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistPublicProducerBidiExact.agda"
)
for file in "${required_files[@]}"; do test -f "$branch_root/$file"; done
grep -q 'zhangPublicProducerReceipt' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastPublicProducerExact.agda"
grep -q '10.5281/zenodo.8093239' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastPublicProducerExact.agda"
grep -q '10.5281/zenodo.8093257' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastPublicProducerExact.agda"
grep -q 'predicted_table_v30.mat' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastPublicProducerExact.agda"
grep -q 'round16ScientificCohortCount = 20' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound16PublicProducerProgressExact.agda"
grep -q 'round16EveryScientistTouched = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound16PublicProducerProgressExact.agda"
grep -q 'publicProducerBindingsCount = 1' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistPublicProducerBidiExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound16PublicProducerProgressExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
echo 'Round-16 public-producer static contract: OK'
