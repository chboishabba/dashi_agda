#!/usr/bin/env bash
set -euo pipefail

branch_root="${1:-.}"

required_files=(
  "DASHI/ComputerScience/ChenShumingGraphHardwareVerificationFiniteWitnessExact.agda"
  "DASHI/Physics/Materials/ZhouGuangyuanPolyimideAerogelFiniteWitnessExact.agda"
  "DASHI/ComputerScience/LiuDonghaoDSMMFiniteWitnessExact.agda"
  "DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastFiniteWitnessExact.agda"
  "DASHI/Control/ZhangDaibingUAVControlFiniteWitnessExact.agda"
  "DASHI/Biology/LiMinyongPhotopharmacologyFiniteWitnessExact.agda"
  "DASHI/Physics/Nuclear/LeBlancFSPICFiniteWitnessExact.agda"
  "DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopyFiniteWitnessExact.agda"
  "DASHI/Physics/Planetary/HicksSmallBodyPhotometryFiniteWitnessExact.agda"
  "DASHI/Biology/JasonThomasSignallingFiniteWitnessExact.agda"
  "DASHI/Physics/ExoticGravity/NingLiYBCOApparatusComparisonFiniteWitnessExact.agda"
  "DASHI/GameTheory/FengYangheClassificationFiniteWitnessExact.agda"
  "DASHI/Physics/Materials/FangDainingInverseDesignFiniteWitnessExact.agda"
  "DASHI/Physics/Aerospace/YanHongThermalExcitationFiniteWitnessExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistScienceFiniteWitnessBidiExact.agda"
)

for file in "${required_files[@]}"; do
  test -f "$branch_root/$file"
done

grep -q 'finiteChenVerificationWitness' "$branch_root/DASHI/ComputerScience/ChenShumingGraphHardwareVerificationFiniteWitnessExact.agda"
grep -q 'finiteZhouAerogelWitness' "$branch_root/DASHI/Physics/Materials/ZhouGuangyuanPolyimideAerogelFiniteWitnessExact.agda"
grep -q 'finiteLiuDSMMWitness' "$branch_root/DASHI/ComputerScience/LiuDonghaoDSMMFiniteWitnessExact.agda"
grep -q 'finiteZhangXiaoxinForecastWitness' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastFiniteWitnessExact.agda"
grep -q 'finiteZhangDaibingControlWitness' "$branch_root/DASHI/Control/ZhangDaibingUAVControlFiniteWitnessExact.agda"
grep -q 'finiteLiMinyongPhotopharmWitness' "$branch_root/DASHI/Biology/LiMinyongPhotopharmacologyFiniteWitnessExact.agda"
grep -q 'finiteLeBlancFSPICWitness' "$branch_root/DASHI/Physics/Nuclear/LeBlancFSPICFiniteWitnessExact.agda"
grep -q 'finiteMaiwaldActionWitness' "$branch_root/DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopyFiniteWitnessExact.agda"
grep -q 'finiteHicksPhotometryWitness' "$branch_root/DASHI/Physics/Planetary/HicksSmallBodyPhotometryFiniteWitnessExact.agda"
grep -q 'finiteThomasSignallingWitness' "$branch_root/DASHI/Biology/JasonThomasSignallingFiniteWitnessExact.agda"
grep -q 'finiteNingApparatusWitness' "$branch_root/DASHI/Physics/ExoticGravity/NingLiYBCOApparatusComparisonFiniteWitnessExact.agda"
grep -q 'finiteFengClassificationWitness' "$branch_root/DASHI/GameTheory/FengYangheClassificationFiniteWitnessExact.agda"
grep -q 'finiteFangInverseDesignWitness' "$branch_root/DASHI/Physics/Materials/FangDainingInverseDesignFiniteWitnessExact.agda"
grep -q 'finiteYanThermalExcitationWitness' "$branch_root/DASHI/Physics/Aerospace/YanHongThermalExcitationFiniteWitnessExact.agda"
grep -q 'round7ScientificCohortCount = 20' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact.agda"
grep -q 'round7EveryScientistTouched = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact.agda"
grep -q 'finiteWitnessDoesNotCreateHistoricalDeployment = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

grep -q 'finiteScienceWitnessBindingsCount = 14' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistScienceFiniteWitnessBidiExact.agda"
grep -q 'syntheticFiniteWitnessCannotPaySourceReplication = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistScienceFiniteWitnessBidiExact.agda"
grep -q 'finiteWitnessCannotPayHistoricalDeployment = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistScienceFiniteWitnessBidiExact.agda"
grep -q 'MissingDeceasedTwentyScientistScienceFiniteWitnessBidiExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

echo 'Round-7 finite-witness static contract: OK'
