#!/usr/bin/env bash
set -euo pipefail

branch_root="${1:-.}"

required_files=(
  "DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastReferenceKernelExact.agda"
  "DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopyReferenceKernelExact.agda"
  "DASHI/Physics/Materials/FangDainingInverseDesignReferenceKernelExact.agda"
  "DASHI/Physics/Aerospace/YanHongThermalExcitationReferenceKernelExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistScienceReferenceKernelBidiExact.agda"
  "DASHI/Culture/MissingDeceasedTwentyScientistRound9ReferenceKernelProgressExact.agda"
)

for file in "${required_files[@]}"; do
  test -f "$branch_root/$file"
done

grep -q 'zhangForecastAggregateKernel' "$branch_root/DASHI/Physics/SpaceWeather/ZhangXiaoxinGeomagneticForecastReferenceKernelExact.agda"
grep -q 'maiwaldSpectralReferenceKernel' "$branch_root/DASHI/Physics/Spectroscopy/MaiwaldActionSpectroscopyReferenceKernelExact.agda"
grep -q 'fangInverseDesignReferenceKernel' "$branch_root/DASHI/Physics/Materials/FangDainingInverseDesignReferenceKernelExact.agda"
grep -q 'yanThermalCaseReferenceKernel' "$branch_root/DASHI/Physics/Aerospace/YanHongThermalExcitationReferenceKernelExact.agda"
grep -q 'referenceKernelBindingsCount = 4' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistScienceReferenceKernelBidiExact.agda"
grep -q 'round9ScientificCohortCount = 20' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound9ReferenceKernelProgressExact.agda"
grep -q 'round9EveryScientistTouched = true' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRound9ReferenceKernelProgressExact.agda"
grep -q 'referenceProjectionDoesNotEqualSourceAlgorithm = false' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistScienceReferenceKernelBidiExact.agda"
grep -q 'MissingDeceasedTwentyScientistRound9ReferenceKernelProgressExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
grep -q 'MissingDeceasedTwentyScientistScienceReferenceKernelBidiExact' "$branch_root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"

echo 'Round-9 reference-kernel static contract: OK'
