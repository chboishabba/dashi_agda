#!/usr/bin/env bash
set -euo pipefail
branch_root="${1:-.}"

required_files=(
  "DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastSourceReplayExact.agda"
  "DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopySourceReplayExact.agda"
  "DASHI/Physics/Materials/FangDainingInverseDesignSourceReplayExact.agda"
  "DASHI/Physics/Aerospace/YanHongThermalExcitationSourceReplayExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistScienceSourceReplayBidiExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistRound8SourceReplayProgressExact.agda"
)
for file in "${required_files[@]}"; do test -f "$branch_root/$file"; done

grep -q 'sourceExactZhangForecastReplay' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastSourceReplayExact.agda"
grep -q '229' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastSourceReplayExact.agda"
grep -q '77.7' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastSourceReplayExact.agda"
grep -q 'sourceExactMaiwaldValineReplay' "$branch_root/DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopySourceReplayExact.agda"
grep -q '1773' "$branch_root/DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopySourceReplayExact.agda"
grep -q 'sourceExactFangInverseDesignReplay' "$branch_root/DASHI/Physics/Materials/FangDainingInverseDesignSourceReplayExact.agda"
grep -q 'negative group velocity' "$branch_root/DASHI/Physics/Materials/FangDainingInverseDesignSourceReplayExact.agda"
grep -q 'sourceExactYanThermalReplay' "$branch_root/DASHI/Physics/Aerospace/YanHongThermalExcitationSourceReplayExact.agda"
grep -q 'E=2 kW, N=2, S=0.02 m' "$branch_root/DASHI/Physics/Aerospace/YanHongThermalExcitationSourceReplayExact.agda"
grep -q 'sourceReplayBindingsCount = 4' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistScienceSourceReplayBidiExact.agda"
grep -q 'round8ScientificCohortCount = 20' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound8SourceReplayProgressExact.agda"
grep -q 'round8EveryScientistTouched = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound8SourceReplayProgressExact.agda"
grep -q 'sourceReplayDoesNotPayHistoricalDeployment = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound8SourceReplayProgressExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound8SourceReplayProgressExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
grep -q 'MissingDeceasedTwentyScientistScienceSourceReplayBidiExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

echo 'Round-8 source-exact replay static contract: OK'
