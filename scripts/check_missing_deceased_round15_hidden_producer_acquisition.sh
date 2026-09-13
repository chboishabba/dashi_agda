#!/usr/bin/env bash
set -euo pipefail
branch_root="${1:-.}"

required_files=(
  "DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopySupportingInfoExact.agda"
  "DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastAlgorithmProducerDepthExact.agda"
  "DASHI/Physics/Aerospace/YanHongThermalFullTextProducerDepthExact.agda"
  "DASHI/Physics/Materials/FangDainingInverseDesignHiddenProducerDebtExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistHiddenProducerBidiExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistRound15HiddenProducerProgressExact.agda"
)

for file in "${required_files[@]}"; do test -f "$branch_root/$file"; done

grep -q 'maiwaldSupportingInfoReceipt' "$branch_root/DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopySupportingInfoExact.agda"
grep -q 'zhangForecastProducerDepth' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinForecastAlgorithmProducerDepthExact.agda"
grep -q 'yanThermalFullTextProducerDepth' "$branch_root/DASHI/Physics/Aerospace/YanHongThermalFullTextProducerDepthExact.agda"
grep -q 'fangHiddenProducerDebt' "$branch_root/DASHI/Physics/Materials/FangDainingInverseDesignHiddenProducerDebtExact.agda"
grep -q 'hiddenProducerBindingsCount = 4' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistHiddenProducerBidiExact.agda"
grep -q 'round15ScientificCohortCount = 20' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound15HiddenProducerProgressExact.agda"
grep -q 'round15EveryScientistTouched = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound15HiddenProducerProgressExact.agda"
grep -q 'hiddenProducerDoesNotPaySourceAlgorithm = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistHiddenProducerBidiExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound15HiddenProducerProgressExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
grep -q 'MissingDeceasedTwentyScientistHiddenProducerBidiExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

echo 'Round-15 hidden-producer static contract: OK'