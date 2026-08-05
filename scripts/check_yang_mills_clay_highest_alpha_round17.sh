#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33BishopInverseDexpActualEndpointModulusExact.agda
  DASHI/Physics/YangMills/BalabanP33DuhamelOrderedSimplexMeasureExact.agda
  DASHI/Physics/YangMills/BalabanClayCoupledPolymerFlowRemainderExact.agda
  DASHI/Physics/YangMills/BalabanClayCoupledRGInvariantConeExact.agda
  DASHI/Physics/YangMills/BalabanClayCouplingPolymerDecouplingCounterexampleExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound17Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round seventeen contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33BishopInverseDexpActualEndpointModulusExact.agda:actualDefectBelowTaylorDefect'
  'BalabanP33BishopInverseDexpActualEndpointModulusExact.agda:actualEndpointDefectNonnegative'
  'BalabanP33BishopInverseDexpActualEndpointModulusExact.agda:actualEndpointDefectQuadraticModulus'
  'BalabanP33DuhamelOrderedSimplexMeasureExact.agda:firstSegmentIntegralExact'
  'BalabanP33DuhamelOrderedSimplexMeasureExact.agda:middleSegmentIntegralExact'
  'BalabanP33DuhamelOrderedSimplexMeasureExact.agda:lastSegmentIntegralExact'
  'BalabanP33DuhamelOrderedSimplexMeasureExact.agda:twoOrderingDuhamelIntegralExact'
  'BalabanClayCoupledPolymerFlowRemainderExact.agda:rawBudgetBelowReducedCoefficientCube'
  'BalabanClayCoupledPolymerFlowRemainderExact.agda:rawBudgetBelowHalfBetaCube'
  'BalabanClayCoupledPolymerFlowRemainderExact.agda:nextCouplingBelowCurrent'
  'BalabanClayCoupledPolymerFlowRemainderExact.agda:nextCouplingNonnegative'
  'BalabanClayCoupledRGInvariantConeExact.agda:coupledInvariantConePreserved'
  'BalabanClayCouplingPolymerDecouplingCounterexampleExact.agda:mixedTermIsHundredDecrements'
  'BalabanClayCouplingPolymerDecouplingCounterexampleExact.agda:couplingDoesNotDecrease'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q 'arXiv:2205.08354' \
  DASHI/Physics/YangMills/BalabanP33BishopInverseDexpActualEndpointModulusExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33BishopInverseDexpActualEndpointModulusExact.agda
grep -q 'arXiv:2606.19362v1' \
  DASHI/Physics/YangMills/BalabanClayCoupledPolymerFlowRemainderExact.agda
grep -q '10.1007/BF01215223' \
  DASHI/Physics/YangMills/BalabanClayCoupledPolymerFlowRemainderExact.agda
grep -q '10.1007/BF01238433' \
  DASHI/Physics/YangMills/BalabanClayCoupledRGInvariantConeExact.agda
grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33DuhamelOrderedSimplexMeasureExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound17Validation.agda
