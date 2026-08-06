#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round27.sh

files=(
  DASHI/Physics/Common/GradedLocalCompatibilitySystemExact.agda
  DASHI/Physics/YangMills/BalabanP33ReflectionPositivityHessianBoundaryExact.agda
  DASHI/Physics/YangMills/BalabanP33TwoPointMomentCurvatureExact.agda
  DASHI/Physics/YangMills/BalabanP33RGGoodClassPreservationExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound28UniformityRoutesValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round twenty eight contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q 'observableRoutesAgree' DASHI/Physics/YangMills/BalabanP33ReflectionPositivityHessianBoundaryExact.agda
grep -q 'candidatesAreDistinct' DASHI/Physics/YangMills/BalabanP33ReflectionPositivityHessianBoundaryExact.agda
grep -q 'twoPointCurvatureIdentity' DASHI/Physics/YangMills/BalabanP33TwoPointMomentCurvatureExact.agda
grep -q 'twoPointCurvatureNonnegative' DASHI/Physics/YangMills/BalabanP33TwoPointMomentCurvatureExact.agda
grep -q 'twoPointCurvatureVanishesOnDiagonal' DASHI/Physics/YangMills/BalabanP33TwoPointMomentCurvatureExact.agda
grep -q 'preserveGoodClass' DASHI/Physics/YangMills/BalabanP33RGGoodClassPreservationExact.agda
grep -q 'twoStepRemainderContractionDirect' DASHI/Physics/YangMills/BalabanP33RGGoodClassPreservationExact.agda
grep -q 'twoStepRemainderContraction' DASHI/Physics/YangMills/BalabanP33RGGoodClassPreservationExact.agda

grep -q '10.48550/arXiv.2205.07376' DASHI/Physics/YangMills/BalabanP33ReflectionPositivityHessianBoundaryExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanP33ReflectionPositivityHessianBoundaryExact.agda
grep -q '10.1007/s00023-013-0303-3' DASHI/Physics/YangMills/BalabanP33RGGoodClassPreservationExact.agda
grep -q '10.1016/S0022-1236(03)00057-0' DASHI/Physics/YangMills/BalabanP33RGGoodClassPreservationExact.agda
grep -q 'generatingFunctionBoundDoesNotAutomaticallyImplyPositiveHessian' DASHI/Physics/YangMills/BalabanP33ReflectionPositivityHessianBoundaryExact.agda
grep -q 'nonnegativeMomentCurvatureDoesNotImplyPositiveHessianFloor' DASHI/Physics/YangMills/BalabanP33TwoPointMomentCurvatureExact.agda
grep -q 'abstractPreservationDoesNotSupplyPhysicalNextStep' DASHI/Physics/YangMills/BalabanP33RGGoodClassPreservationExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound28UniformityRoutesValidation.agda
