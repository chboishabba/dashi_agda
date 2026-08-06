#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_commutator_continuum_round14.sh

files=(
  DASHI/Physics/Common/FiniteProjectionOffDiagonalExact.agda
  DASHI/Physics/Common/ReducedModeProjectionExact.agda
  DASHI/Physics/Common/FiftyThreeTypedBoundaryExact.agda
  DASHI/Physics/Common/WeightedStrictLossTransportExact.agda
  DASHI/Physics/Common/CoarseDynamicsCommutatorExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoProjectionLeakageCrossPollinationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoStrictLossCrossPollinationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoClayCrossPollinationRound15Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "NS cross-pollination tranche contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'FiniteProjectionOffDiagonalExact.agda:projectionCommutatorExact'
  'FiniteProjectionOffDiagonalExact.agda:projectionCommutatorNormSqExact'
  'FiniteProjectionOffDiagonalExact.agda:symmetricCouplingLeakageSqExact'
  'ReducedModeProjectionExact.agda:fieldReconstructsFromConstantAndMeanZero'
  'ReducedModeProjectionExact.agda:constantMeanZeroOrthogonal'
  'ReducedModeProjectionExact.agda:sixByNineReducedModeCount'
  'FiftyThreeTypedBoundaryExact.agda:highLowKernelPartitionExact'
  'FiftyThreeTypedBoundaryExact.agda:fiftyThreeOccurrencesRemainTypeDistinct'
  'WeightedStrictLossTransportExact.agda:pullBackClosedForm'
  'WeightedStrictLossTransportExact.agda:strictMarginBelowPullBack'
  'CoarseDynamicsCommutatorExact.agda:neutralResidualImpliesExactAt'
  'NSTriadKNLuoProjectionLeakageCrossPollinationExact.agda:transportCommutatorIsProjectionLeakage'
  'NSTriadKNLuoProjectionLeakageCrossPollinationExact.agda:oppositeHelicityEigenvaluesCancel'
  'NSTriadKNLuoStrictLossCrossPollinationExact.agda:fourClassStrictBudgetImpliesPositiveFloor'
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
grep -q '10.1002/cpa.3160410704' DASHI/Physics/Closure/NSTriadKNLuoProjectionLeakageCrossPollinationExact.agda
grep -q '10.1007/s00041-018-9612-8' DASHI/Physics/Closure/NSTriadKNLuoProjectionLeakageCrossPollinationExact.agda
grep -q '10.1063/1.858309' DASHI/Physics/Closure/NSTriadKNLuoProjectionLeakageCrossPollinationExact.agda
grep -q '10.1090/cbms/092' DASHI/Physics/Common/ReducedModeProjectionExact.agda
grep -q '10.24033/asens.1404' DASHI/Physics/Closure/NSTriadKNLuoStrictLossCrossPollinationExact.agda
grep -q 'projectionIdentitySuppliesContinuumSixThreeBoundIsFalse' DASHI/Physics/Closure/NSTriadKNLuoProjectionLeakageCrossPollinationExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoClayCrossPollinationRound15Validation.agda
