#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_conscious_access_round7_harmonic_wreath_carrier.sh

files=(
  DASHI/Physics/Common/GradedLocalCompatibilitySystemExact.agda
  DASHI/Biology/MoonshineVacuumConformalLineBoundaryExact.agda
  DASHI/Biology/MoonshineConformalReductionVsFiftyFourReductionExact.agda
  DASHI/Biology/FiniteGradedModeCarrierExact.agda
  DASHI/Biology/MoonshineWeightTwoGriessProductSchemaExact.agda
  DASHI/Biology/MoonshineGradedTraceProbeExact.agda
  DASHI/Biology/MoonshineShiftedJCoefficientBoundaryExact.agda
  DASHI/Biology/MonsterLieAlgebraGradeBoundaryExact.agda
  DASHI/Biology/ConsciousAccessRound8VOAGradeSemanticsValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round eight contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'GradedLocalCompatibilitySystemExact.agda:localOperationGradeStable'
  'GradedLocalCompatibilitySystemExact.agda:transportDefectTwice'
  'MoonshineVacuumConformalLineBoundaryExact.agda:weightTwoDimensionExact'
  'MoonshineVacuumConformalLineBoundaryExact.agda:vacuumIsNotConformal'
  'MoonshineVacuumConformalLineBoundaryExact.agda:conformalIsNotCompletion'
  'MoonshineConformalReductionVsFiftyFourReductionExact.agda:moonshineWeightTwoReduction'
  'MoonshineConformalReductionVsFiftyFourReductionExact.agda:fiftyFourToFiftyThreeReduction'
  'MoonshineConformalReductionVsFiftyFourReductionExact.agda:removedLinesAreDistinct'
  'FiniteGradedModeCarrierExact.agda:weightTwoFirstModeClosure'
  'FiniteGradedModeCarrierExact.agda:weightTwoFirstModeOutputIsTwo'
  'MoonshineWeightTwoGriessProductSchemaExact.agda:fullWeightTwoDimensionExact'
  'MoonshineWeightTwoGriessProductSchemaExact.agda:weightTwoFirstProductClosesInWeightTwo'
  'MoonshineGradedTraceProbeExact.agda:identityTraceProbesSeparate'
  'MoonshineGradedTraceProbeExact.agda:moonshineWeightTwoTraceExact'
  'MoonshineGradedTraceProbeExact.agda:bothRoutesRequireGriessWeightTwo'
  'MoonshineShiftedJCoefficientBoundaryExact.agda:centralChargeShiftExact'
  'MoonshineShiftedJCoefficientBoundaryExact.agda:traceProfileMatchesShiftedCoefficients'
  'MonsterLieAlgebraGradeBoundaryExact.agda:voaZeroIsNotMonsterLieOrigin'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  if [[ -f "DASHI/Biology/$file" ]]; then
    grep -q "$theorem" "DASHI/Biology/$file"
  else
    grep -q "$theorem" "DASHI/Physics/Common/$file"
  fi
done

grep -q '10.1007/978-0-8176-8186-9' DASHI/Biology/FiniteGradedModeCarrierExact.agda
grep -q '10.1353/ajm.2007.0009' DASHI/Biology/MoonshineGradedTraceProbeExact.agda
grep -q '10.1007/BF01389186' DASHI/Biology/MoonshineWeightTwoGriessProductSchemaExact.agda
grep -q '10.1112/blms/11.3.308' DASHI/Biology/MoonshineShiftedJCoefficientBoundaryExact.agda
grep -q '10.1007/BF01614075' DASHI/Biology/MonsterLieAlgebraGradeBoundaryExact.agda
grep -q 'weightTwoOneIsNotVacuumLine' DASHI/Biology/MoonshineVacuumConformalLineBoundaryExact.agda
grep -q 'concreteLinesNotIdentified' DASHI/Biology/MoonshineConformalReductionVsFiftyFourReductionExact.agda
grep -q 'constituentOnlyIsNotDeclaredFullGriessAlgebra' DASHI/Biology/MoonshineWeightTwoGriessProductSchemaExact.agda
grep -q 'truncatedIdentityTraceDoesNotDetermineVOA' DASHI/Biology/MoonshineGradedTraceProbeExact.agda
grep -q 'threeInitialCoefficientsDoNotProveGenusZero' DASHI/Biology/MoonshineShiftedJCoefficientBoundaryExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound8VOAGradeSemanticsValidation.agda
