#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
combined="$root/DASHI/Culture/MissingDeceasedCombinedRocketScramjetVehicleBidiExact.agda"
space="$root/DASHI/Culture/MissingDeceasedSpaceFissionResearchPlatformBidiExact.agda"
high="$root/DASHI/Culture/MissingDeceasedHighEnergyExperimentalFacilityBidiExact.agda"
bio="$root/DASHI/Culture/MissingDeceasedMolecularBiologyResearchPlatformBidiExact.agda"
matrix="$root/DASHI/Culture/MissingDeceasedTwentyScientistRealObjectIncidenceExact.agda"
round18="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound18RealObjectProgressExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

for f in "$combined" "$space" "$high" "$bio" "$matrix" "$round18" "$agg"; do
  test -f "$f"
done

grep -q 'boosterRocketObject' "$combined"
grep -q 'airbreathingObject' "$combined"
grep -q 'commonVehicleObject' "$combined"
grep -q 'rocketOxidizerAndScramjetAirAreDifferentInputs = true' "$combined"
grep -q 'rocketBoostAndScramjetCruiseCanShareVehicle = true' "$combined"
grep -q 'rezaBoosterFit' "$combined"
grep -q 'yanAirbreathingFit' "$combined"

grep -q 'spaceFissionResearchPlatform' "$space"
grep -q 'leblancFissionPowerFit' "$space"
grep -q 'zhangXiaoxinSpaceWeatherFit' "$space"

grep -q 'highEnergyExperimentalFacility' "$high"
grep -q 'chavezRadiographyFit' "$high"
grep -q 'ningPrecisionForceFit' "$high"

grep -q 'molecularBiologyResearchPlatform' "$bio"
grep -q 'maiwaldMolecularDiagnosticsFit' "$bio"
grep -q 'jasonThomasChemicalBiologyFit' "$bio"
grep -q 'liMinyongPhotopharmacologyFit' "$bio"

grep -q 'record RealObjectIncidenceRow' "$matrix"
grep -q 'twentyScientistRealObjectIncidence' "$matrix"
grep -q 'realObjectIncidenceScientistCount = 20' "$matrix"
grep -q 'incidenceFitPaysHistoricalParticipation = false' "$matrix"
grep -q 'incidenceFitPaysH2 = false' "$matrix"

for name in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$name" "$matrix"
  grep -q "$name" "$round18"
done

grep -q 'round18ScientificCohortCount = 20' "$round18"
grep -q 'round18EveryScientistTouched = true' "$round18"
grep -q 'round18HistoricalParticipationPromotionCount = 0' "$round18"
grep -q 'round18H2PromotionCount = 0' "$round18"
grep -q 'round18H3PromotionCount = 0' "$round18"

grep -q 'MissingDeceasedCombinedRocketScramjetVehicleBidiExact' "$agg"
grep -q 'MissingDeceasedTwentyScientistRealObjectIncidenceExact' "$agg"
grep -q 'MissingDeceasedTwentyScientistRound18RealObjectProgressExact' "$agg"

echo 'Round18 real-object incidence static contract: OK'
