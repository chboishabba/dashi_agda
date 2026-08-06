#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33BishopInverseDexpPositiveDenominatorExact.agda
  DASHI/Physics/YangMills/BalabanP33InverseDexpEndpointModulusExact.agda
  DASHI/Physics/YangMills/BalabanP33QuaternionChordalSquaredExact.agda
  DASHI/Physics/YangMills/BalabanP33DuhamelSecondDerivativeMajorantExact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109LocalLeafCalibrationExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonSharpDuhamelBudgetExact.agda
  DASHI/Physics/YangMills/BalabanClayStrictMacrostepComponentAssemblyExact.agda
  DASHI/Physics/YangMills/BalabanClayDyadicCutoffTailExact.agda
  DASHI/Physics/YangMills/BalabanClayOneLoopFlowRemainderExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound16Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round sixteen contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33BishopInverseDexpPositiveDenominatorExact.agda:positiveSineOnPositiveHalfBall'
  'BalabanP33BishopInverseDexpPositiveDenominatorExact.agda:inverseDexpDenominatorPositive'
  'BalabanP33BishopInverseDexpPositiveDenominatorExact.agda:positiveInverseDexpCoefficientBounds'
  'BalabanP33BishopInverseDexpPositiveDenominatorExact.agda:inverseDexpCoefficientAtZero'
  'BalabanP33InverseDexpEndpointModulusExact.agda:endpointDefectExact'
  'BalabanP33InverseDexpEndpointModulusExact.agda:endpointDefectQuadraticModulus'
  'BalabanP33QuaternionChordalSquaredExact.agda:quaternionMultiplyDistributesRight'
  'BalabanP33QuaternionChordalSquaredExact.agda:chordSquaredLeftInvariant'
  'BalabanP33QuaternionChordalSquaredExact.agda:chordSquaredRightInvariant'
  'BalabanP33DuhamelSecondDerivativeMajorantExact.agda:threeExponentialDefectMajorantExact'
  'BalabanP33DuhamelSecondDerivativeMajorantExact.agda:secondDerivativeDuhamelMajorantExact'
  'BalabanP33CMP109LocalLeafCalibrationExact.agda:completeCMP109AllocationIsRadius'
  'BalabanP33WilsonSharpDuhamelBudgetExact.agda:sharpBudgetPlusSlackIsRadius'
  'BalabanClayStrictMacrostepComponentAssemblyExact.agda:strictMacrostepFromFiveMechanisms'
  'BalabanClayStrictMacrostepComponentAssemblyExact.agda:largeFieldLeavesPositiveGaussian'
  'BalabanClayDyadicCutoffTailExact.agda:finiteDistanceBelowDoubleDyadic'
  'BalabanClayOneLoopFlowRemainderExact.agda:nextNonnegative'
  'BalabanClayOneLoopFlowRemainderExact.agda:nextBelowCurrent'
  'BalabanClayOneLoopFlowRemainderExact.agda:crossMultipliedReciprocalGain'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33BishopInverseDexpPositiveDenominatorExact.agda
grep -q 'arXiv:2205.08354' \
  DASHI/Physics/YangMills/BalabanP33BishopInverseDexpPositiveDenominatorExact.agda
grep -q '10.1017/CBO9781139020411' \
  DASHI/Physics/YangMills/BalabanP33QuaternionChordalSquaredExact.agda
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33WilsonSharpDuhamelBudgetExact.agda
grep -q '10.1007/BF01238433' \
  DASHI/Physics/YangMills/BalabanClayStrictMacrostepComponentAssemblyExact.agda
grep -q '10.1103/PhysRevLett.30.1343' \
  DASHI/Physics/YangMills/BalabanClayOneLoopFlowRemainderExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound16Validation.agda
