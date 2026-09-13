#!/usr/bin/env bash
set -euo pipefail

branch_root="${1:-.}"

required_files=(
  "DASHI/Physics/ExoticGravity/NingLiYBCOSourceDataReplayExact.agda"
  "DASHI/Physics/Materials/ZhouGuangyuanAerogelProcessPropertyDataReplayExact.agda"
  "DASHI/Physics/Planetary/HicksSmallBodyPhotometryDataReplayExact.agda"
  "DASHI/Biology/JasonThomasAssayDataReplayExact.agda"
  "DASHI/Control/ZhangDaibingControlDataReplayExact.agda"
  "DASHI/GameTheory/FengYangheClassificationDataReplayExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistScienceSourceDataReplayBidiExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistRound14SourceDataReplayProgressExact.agda"
)

for file in "${required_files[@]}"; do
  test -f "$branch_root/$file"
done

grep -q 'ningSourceDataReplay' "$branch_root/DASHI/Physics/ExoticGravity/NingLiYBCOSourceDataReplayExact.agda"
grep -q 'zhouProcessPropertyDataReplay' "$branch_root/DASHI/Physics/Materials/ZhouGuangyuanAerogelProcessPropertyDataReplayExact.agda"
grep -q 'hicksPhotometryDataReplay' "$branch_root/DASHI/Physics/Planetary/HicksSmallBodyPhotometryDataReplayExact.agda"
grep -q 'thomasAssayDataReplay' "$branch_root/DASHI/Biology/JasonThomasAssayDataReplayExact.agda"
grep -q 'zhangDaibingControlDataReplay' "$branch_root/DASHI/Control/ZhangDaibingControlDataReplayExact.agda"
grep -q 'fengClassificationDataReplay' "$branch_root/DASHI/GameTheory/FengYangheClassificationDataReplayExact.agda"
grep -q 'sourceDataReplayBindingsCount = 6' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistScienceSourceDataReplayBidiExact.agda"
grep -q 'numericSourceDataAndBlockedRowsRemainDistinct = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistScienceSourceDataReplayBidiExact.agda"
grep -q 'sourceDataBindingDoesNotPayHistoricalUse = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistScienceSourceDataReplayBidiExact.agda"
grep -q 'round14ScientificCohortCount = 20' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound14SourceDataReplayProgressExact.agda"
grep -q 'round14EveryScientistTouched = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound14SourceDataReplayProgressExact.agda"
grep -q 'round14SourceDataReplayPromotionCount = 6' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound14SourceDataReplayProgressExact.agda"
grep -q 'sourceDataReplayDoesNotPayHistoricalDeployment = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound14SourceDataReplayProgressExact.agda"
grep -q 'sourceDataReplayDoesNotPayCustody = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound14SourceDataReplayProgressExact.agda"
grep -q 'MissingDeceasedTwentyScientistScienceSourceDataReplayBidiExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
grep -q 'MissingDeceasedTwentyScientistRound14SourceDataReplayProgressExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

echo 'Round-14 source-data replay static contract: OK'
