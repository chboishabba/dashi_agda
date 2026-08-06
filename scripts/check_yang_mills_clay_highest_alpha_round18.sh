#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33BishopQuaternionExponentialSquaredChordExact.agda
  DASHI/Physics/YangMills/BalabanP33BishopLiteralQuaternionExponentialChordExact.agda
  DASHI/Physics/YangMills/BalabanP33BishopR4ChordMetricFromSquareRootExact.agda
  DASHI/Physics/YangMills/BalabanP33QuaternionDuhamelIntegrandTelescopeExact.agda
  DASHI/Physics/YangMills/BalabanP33DuhamelSecondDerivativeMajorantExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteQuaternionSimpleDuhamelIntegralExact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109LiteralPathDerivativeKernelExact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109PeriodicContourEdgeKernelExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintSecondVariationExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralHessianFiveChannelPromotionExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralResidualKernelNumericalCalibrationExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalResidualHalfContractionAtCollar21Exact.agda
  DASHI/Physics/YangMills/BalabanClayPhysicalCoupledMacrostepPromotionExact.agda
  DASHI/Physics/YangMills/BalabanClayDyadicPhysicalClusteringExponentExact.agda
  DASHI/Physics/YangMills/BalabanClayPlaquetteNoncollapseContinuumCalibrationExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound18Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round eighteen contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33BishopQuaternionExponentialSquaredChordExact.agda:actualSquaredChordBelowRadiusSquared'
  'BalabanP33BishopLiteralQuaternionExponentialChordExact.agda:sincExtendedCancellation'
  'BalabanP33BishopLiteralQuaternionExponentialChordExact.agda:literalExponentialSquaredChordBelowRadiusSquared'
  'BalabanP33BishopR4ChordMetricFromSquareRootExact.agda:lagrangeIdentity4'
  'BalabanP33BishopR4ChordMetricFromSquareRootExact.agda:cauchySchwarzSquared4'
  'BalabanP33BishopR4ChordMetricFromSquareRootExact.agda:literalChordDistanceTriangle'
  'BalabanP33BishopR4ChordMetricFromSquareRootExact.agda:literalExponentialChordDistanceBelowRadius'
  'BalabanP33QuaternionDuhamelIntegrandTelescopeExact.agda:orderedDuhamelIntegrandTelescopeExact'
  'BalabanP33FiniteQuaternionSimpleDuhamelIntegralExact.agda:finiteSymmetricSimpleIntegralTelescopeExact'
  'BalabanP33CMP109LiteralPathDerivativeKernelExact.agda:cmp109PathDerivativeVanishesOutsideLiteralOccurrence'
  'BalabanP33CMP109PeriodicContourEdgeKernelExact.agda:orientationInsertion'
  'BalabanP33CMP109PeriodicContourEdgeKernelExact.agda:occurrenceHolonomyEqualsPeriodicWordHolonomy'
  'BalabanP33CMP109PeriodicContourEdgeKernelExact.agda:orientedContourDerivativeZeroOutsideUnderlyingSupport'
  'BalabanP33LiteralGaugeConstraintSecondVariationExact.agda:literalTotalSecondVariationAtExactBackground'
  'BalabanP33LiteralHessianFiveChannelPromotionExact.agda:literalHessianCoerciveOneThirtySecond'
  'BalabanP33LiteralResidualKernelNumericalCalibrationExact.agda:literalResidualEntryExact'
  'BalabanP33LiteralResidualKernelNumericalCalibrationExact.agda:physicalCoordinateCount'
  'BalabanP33LiteralResidualKernelNumericalCalibrationExact.agda:fullRowSupportRadiusExact'
  'BalabanP33LiteralResidualKernelNumericalCalibrationExact.agda:collar21HalfContractionArithmetic'
  'BalabanP33PhysicalResidualHalfContractionAtCollar21Exact.agda:physicalResidualHalfRowBound'
  'BalabanClayPhysicalCoupledMacrostepPromotionExact.agda:physicalCoupledMacrostepConclusions'
  'BalabanClayDyadicPhysicalClusteringExponentExact.agda:latticeExponentIsPhysicalExponent'
  'BalabanClayPlaquetteNoncollapseContinuumCalibrationExact.agda:continuumOSNormStrictlyPositive'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Provenance and terminology checks.  In particular, do not regress to the
# unrelated geometric "Bochner identity" as the name of the Duhamel producer.
grep -q '10.1007/978-3-642-61667-9' \
  DASHI/Physics/YangMills/BalabanP33BishopR4ChordMetricFromSquareRootExact.agda
grep -q '10.1090/SURV/015' \
  DASHI/Physics/YangMills/BalabanP33DuhamelSecondDerivativeMajorantExact.agda
grep -q '10.1007/978-3-0348-5567-9' \
  DASHI/Physics/YangMills/BalabanP33QuaternionDuhamelIntegrandTelescopeExact.agda
grep -q 'Bochner-integral Duhamel' \
  DASHI/Physics/YangMills/BalabanP33DuhamelSecondDerivativeMajorantExact.agda
grep -q '10.1007/BF01211042' \
  DASHI/Physics/YangMills/BalabanP33CMP109PeriodicContourEdgeKernelExact.agda
grep -q '10.1007/BF01466594' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintSecondVariationExact.agda
grep -q '3072' \
  DASHI/Physics/YangMills/BalabanP33LiteralResidualKernelNumericalCalibrationExact.agda
grep -q '2097152' \
  DASHI/Physics/YangMills/BalabanP33LiteralResidualKernelNumericalCalibrationExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound18Validation.agda
