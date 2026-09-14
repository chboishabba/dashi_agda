#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
core="$root/DASHI/Core/RealObjectApplicationBidiExact.agda"
obj="$root/DASHI/Culture/MissingDeceasedHypersonicAirbreathingVehicleBidiExact.agda"
round="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound17HypersonicObjectProgressExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$core"
test -f "$obj"
test -f "$round"
test -f "$agg"

grep -q 'data FitStrength' "$core"
grep -q 'directSourceFit' "$core"
grep -q 'engineeringTransfer' "$core"
grep -q 'methodTransfer' "$core"
grep -q 'analogyOnly' "$core"
grep -q 'noFit' "$core"
grep -q 'record RealObjectRequirement' "$core"
grep -q 'record ScientistObjectFit' "$core"
grep -q 'record RealEngineeringObject' "$core"
grep -q 'subsystemFitPaysHistoricalParticipation = false' "$core"
grep -q 'multipleFitsPayCommonProgramme = false' "$core"
grep -q 'engineeringTransferPaysQualification = false' "$core"
grep -q 'methodTransferPaysDeployedImplementation = false' "$core"
grep -q 'realObjectFitPaysEventCause = false' "$core"
grep -q 'realObjectFitPaysH2 = false' "$core"
grep -q 'noFitCanReduceInventedInterfaceDebt = true' "$core"

grep -q 'data HypersonicSubsystem' "$obj"
grep -q 'inletCompression' "$obj"
grep -q 'shockBoundaryLayerControl' "$obj"
grep -q 'supersonicCombustion' "$obj"
grep -q 'thermalProtection' "$obj"
grep -q 'faultTolerantControl' "$obj"
grep -q 'hardwareVerification' "$obj"
grep -q 'guidanceAutonomy' "$obj"
grep -q 'hypersonicSourceAtlas' "$obj"
grep -q 'yanHongFit' "$obj"
grep -q 'fangDainingFit' "$obj"
grep -q 'zhouGuangyuanFit' "$obj"
grep -q 'monicaRezaFit' "$obj"
grep -q 'mccaslandFit' "$obj"
grep -q 'chenShumingFit' "$obj"
grep -q 'zhangDaibingFit' "$obj"
grep -q 'inletCompressionPaysAirLiquefaction = false' "$obj"
grep -q 'scramjetCarriesOxidizerLikeRocket = false' "$obj"
grep -q 'rocketAndScramjetAreSameThermodynamicObject = false' "$obj"
grep -q 'rocketBoostPlusScramjetCruiseCanCoexist = true' "$obj"
grep -q 'oxygenServiceAlloyPaysScramjetQualification = false' "$obj"
grep -q 'hypersonicRelevancePaysWeaponProgramme = false' "$obj"

for person in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$person" "$round"
done

grep -q 'round17ScientificCohortCount = 20' "$round"
grep -q 'round17EveryScientistTouched = true' "$round"
grep -q 'round17StrongFitCount = 7' "$round"
grep -q 'round17HistoricalParticipationPromotionCount = 0' "$round"
grep -q 'round17H2PromotionCount = 0' "$round"
grep -q 'round17H3PromotionCount = 0' "$round"
grep -q 'round17NoFitReducesInventedInterfaceDebt = true' "$round"

grep -q 'MissingDeceasedHypersonicAirbreathingVehicleBidiExact' "$agg"
grep -q 'MissingDeceasedTwentyScientistRound17HypersonicObjectProgressExact' "$agg"

echo 'Round17 hypersonic real-object BIDI static contract: OK'
