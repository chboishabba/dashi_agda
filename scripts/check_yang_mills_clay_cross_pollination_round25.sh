#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round24.sh

files=(
  DASHI/Physics/Common/FiniteProjectionOffDiagonalExact.agda
  DASHI/Physics/Common/ReducedModeProjectionExact.agda
  DASHI/Physics/Common/FiftyThreeTypedBoundaryExact.agda
  DASHI/Physics/Common/WeightedStrictLossTransportExact.agda
  DASHI/Physics/Common/CoarseDynamicsCommutatorExact.agda
  DASHI/Physics/YangMills/BalabanP33ProjectionSchurCrossPollinationExact.agda
  DASHI/Physics/YangMills/BalabanP33GaugeModeRGResidualCrossPollinationExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound25CrossPollinationValidation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "YM cross-pollination tranche contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'FiniteProjectionOffDiagonalExact.agda:projectionCommutatorExact'
  'FiniteProjectionOffDiagonalExact.agda:projectionCommutatorNormSqExact'
  'ReducedModeProjectionExact.agda:meanZeroProjectionIdempotent'
  'ReducedModeProjectionExact.agda:sixByNineReducedModeCount'
  'FiftyThreeTypedBoundaryExact.agda:highLowKernelPartitionExact'
  'FiftyThreeTypedBoundaryExact.agda:fiftyThreeOccurrencesRemainTypeDistinct'
  'WeightedStrictLossTransportExact.agda:strictMarginBelowPullBack'
  'CoarseDynamicsCommutatorExact.agda:neutralResidualImpliesExactAt'
  'BalabanP33ProjectionSchurCrossPollinationExact.agda:schurCoefficientFactorsThroughProjectionLeakage'
  'BalabanP33ProjectionSchurCrossPollinationExact.agda:sharedStrictMarginBelowYMOneStep'
  'BalabanP33GaugeModeRGResidualCrossPollinationExact.agda:effectiveSchurIsDefectControlledObservation'
  'BalabanP33GaugeModeRGResidualCrossPollinationExact.agda:effectiveResidualVanishesExactlyWhenSquareCommutes'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  match="$(find DASHI/Physics -name "$file" -print -quit)"
  test -n "$match"
  grep -q "$theorem" "$match"
done

# Source metadata and authority boundaries.
grep -q '10.1017/CBO9781139020411' DASHI/Physics/Common/FiniteProjectionOffDiagonalExact.agda
grep -q '10.1016/S0022-1236(03)00057-0' DASHI/Physics/Common/FiniteProjectionOffDiagonalExact.agda
grep -q '10.1007/BF01240221' DASHI/Physics/YangMills/BalabanP33ProjectionSchurCrossPollinationExact.agda
grep -q '10.1007/BF01466594' DASHI/Physics/YangMills/BalabanP33GaugeModeRGResidualCrossPollinationExact.agda
grep -q '10.1016/j.matpur.2012.02.001' DASHI/Physics/YangMills/BalabanP33GaugeModeRGResidualCrossPollinationExact.agda
grep -q 'sharedAlgebraSuppliesPhysicalBAndCInverseBoundsIsFalse' DASHI/Physics/YangMills/BalabanP33ProjectionSchurCrossPollinationExact.agda

a="DASHI/Physics/YangMills/BalabanClayHighestAlphaRound25CrossPollinationValidation.agda"
scripts/run_agda29_parallel_check.sh "$a"
