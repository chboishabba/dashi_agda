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
  "DASHI/Culture/MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact.agda"
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
grep -q 'round7ScientificCohortCount = 20' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact.agda"
grep -q 'round7EveryScientistTouched = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact.agda"
grep -q 'finiteWitnessDoesNotCreateHistoricalDeployment = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound7FiniteWitnessProgressExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

for import_name in \
  ChenShumingGraphHardwareVerificationFiniteWitnessExact \
  ZhouGuangyuanPolyimideAerogelFiniteWitnessExact \
  LiuDonghaoDSMMFiniteWitnessExact \
  ZhangXiaoxinGeomagneticForecastFiniteWitnessExact \
  ZhangDaibingUAVControlFiniteWitnessExact \
  LiMinyongPhotopharmacologyFiniteWitnessExact; do
  grep -q "$import_name" "$branch_root/DASHI/Culture/MissingDeceasedChineseScienceImplementationEverything.agda"
done

echo 'Round-7 finite-witness static contract: OK'
