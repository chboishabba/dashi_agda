#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"

required=(
  "$root/DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopySourceReplayDepthExact.agda"
  "$root/DASHI/Physics/Materials/ZhouGuangyuanAerogelProcessPropertySourceReplayExact.agda"
  "$root/DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastSourceReplayDepthExact.agda"
  "$root/DASHI/Physics/Astrophysics/GrillmairStellarStreamSourceReplayExact.agda"
  "$root/DASHI/Physics/Planetary/HicksSmallBodyPhotometrySourceReplayExact.agda"
  "$root/DASHI/Culture/MissingDeceasedTwentyScientistRound11SourceReplayParetoExact.agda"
)
for f in "${required[@]}"; do test -f "$f"; done

grep -q 'maiwaldDepthReplay' "$root/DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopySourceReplayDepthExact.agda"
grep -q 'zhouProcessPropertyReplay' "$root/DASHI/Physics/Materials/ZhouGuangyuanAerogelProcessPropertySourceReplayExact.agda"
grep -q 'zhangForecastDepthReplay' "$root/DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastSourceReplayDepthExact.agda"
grep -q 'grillmairStreamReplay' "$root/DASHI/Physics/Astrophysics/GrillmairStellarStreamSourceReplayExact.agda"
grep -q 'hicksPhotometryReplay' "$root/DASHI/Physics/Planetary/HicksSmallBodyPhotometrySourceReplayExact.agda"

grep -q 'sourceReplayBindingsCount = 9' "$root/DASHI/Culture/MissingDeceasedTwentyScientistScienceSourceReplayBidiExact.agda"
grep -q 'sourceReplayRuntimeSlotCount = 7' "$root/DASHI/Culture/MissingDeceasedTwentyScientistEmbodiedReferenceRuntimeBidiExact.agda"
grep -q 'round11ScientificCohortCount = 20' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRound11SourceReplayParetoExact.agda"
grep -q 'round11EveryScientistTouched = true' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRound11SourceReplayParetoExact.agda"
grep -q 'round11NewReplayPromotionCount = 5' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRound11SourceReplayParetoExact.agda"
grep -q 'sourceReplayDoesNotPayCustody = false' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRound11SourceReplayParetoExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound11SourceReplayParetoExact' "$root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

grep -q '"Carl J. Grillmair": {"role": "astronomical_inference", "ready": True, "source_replay": True' "$root/scripts/twenty_scientist_embodied_reference_runtime.py"
grep -q '"Michael David Hicks": {"role": "planetary_characterisation", "ready": True, "source_replay": True' "$root/scripts/twenty_scientist_embodied_reference_runtime.py"
grep -q '"Zhou Guangyuan": {"role": "thermal_protection", "ready": True, "source_replay": True' "$root/scripts/twenty_scientist_embodied_reference_runtime.py"

echo 'Round-11 source-replay Pareto static contract: OK'
