#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

# Validate the complete stacked predecessor first.
bash scripts/check_yang_mills_clay_cross_pollination_round25.sh

files=(
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalGapScaleInvarianceExact.agda
  DASHI/Physics/YangMills/BalabanP33KernelDecayToSchurExact.agda
  DASHI/Physics/YangMills/BalabanP33UniformSchurFeedbackFromDecayExact.agda
  DASHI/Physics/YangMills/BalabanP33StageIStageIISpectralBoundaryExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound26Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

test -f .github/workflows/yang-mills-clay-highest-alpha-round26.yml

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round twenty-six contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda:weightedSquareWithReciprocalExact'
  'BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda:weightedDifferenceLower'
  'BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda:pointwiseGaugeEnergyDifferenceLower'
  'BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda:backgroundGaugeEnergyDifferenceLower'
  'BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda:backgroundGaugeSignedLowerParameterized'
  'BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda:relaxedCoefficientExact'
  'BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda:backgroundGaugeSignedLowerSixtyFourRelaxed'
  'BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda:backgroundGaugeResidualSignedLowerSixtyFourRelaxed'
  'BalabanP33PhysicalGapScaleInvarianceExact.agda:physicalGapPreservedByExactDyadicStep'
  'BalabanP33PhysicalGapScaleInvarianceExact.agda:physicalRatioCrossProductInvariant'
  'BalabanP33PhysicalGapScaleInvarianceExact.agda:physicalGapAtEveryDyadicDepth'
  'BalabanP33PhysicalGapScaleInvarianceExact.agda:splitGapAfterLossBelowTwiceFine'
  'BalabanP33PhysicalGapScaleInvarianceExact.agda:lossCorrectedPhysicalCrossProduct'
  'BalabanP33KernelDecayToSchurExact.agda:kernelMajorantRowMass'
  'BalabanP33KernelDecayToSchurExact.agda:kernelMajorantColumnMass'
  'BalabanP33KernelDecayToSchurExact.agda:kernelMajorantSchurSquared'
  'BalabanP33UniformSchurFeedbackFromDecayExact.agda:feedbackDecayCoefficientExpanded'
  'BalabanP33UniformSchurFeedbackFromDecayExact.agda:uniformSchurFeedbackFromDecay'
  'BalabanP33StageIStageIISpectralBoundaryExact.agda:physicalDyadicGapCompatibility'
  'BalabanP33StageIStageIISpectralBoundaryExact.agda:stageIIScaleNormalizationAlgebraLevel'
  'BalabanP33StageIStageIISpectralBoundaryExact.agda:stageIIPhysicalDyadicCompatibilityLevel'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Primary-source and stress-test metadata.
grep -q '10.1007/BF01466594' \
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda
grep -q '10.1017/CBO9781316036440' \
  DASHI/Physics/YangMills/BalabanP33PhysicalGapScaleInvarianceExact.agda
grep -q '10.1007/BF01240221' \
  DASHI/Physics/YangMills/BalabanP33PhysicalGapScaleInvarianceExact.agda
grep -q '10.1007/s00023-013-0303-3' \
  DASHI/Physics/YangMills/BalabanP33PhysicalGapScaleInvarianceExact.agda
grep -q 'ai.viXra:2602.0033' \
  DASHI/Physics/YangMills/BalabanP33PhysicalGapScaleInvarianceExact.agda
grep -q '10.1007/BF01646473' \
  DASHI/Physics/YangMills/BalabanP33KernelDecayToSchurExact.agda
grep -q '10.1016/S0022-1236(03)00057-0' \
  DASHI/Physics/YangMills/BalabanP33UniformSchurFeedbackFromDecayExact.agda

# Scope and hard-math guards.
grep -q 'delta = 4 rho\^2' \
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda
grep -q 'physicalRelaxedInverseLinkRadiusProducerLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda
grep -q 'physicalTransferMatrixDyadicCompatibilityLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalGapScaleInvarianceExact.agda
grep -q 'physicalUniformFluctuationInverseLocalityLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalGapScaleInvarianceExact.agda
grep -q 'physicalUniformCoarseFineCouplingLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalGapScaleInvarianceExact.agda
grep -q 'physicalUniformFluctuationInverseDecayProducerLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33KernelDecayToSchurExact.agda
grep -q 'physicalUniformCouplingDecayInputLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33UniformSchurFeedbackFromDecayExact.agda
grep -q 'scaleAlgebraAutomaticallyProvesPhysicalDoublingIsFalse' \
  DASHI/Physics/YangMills/BalabanP33StageIStageIISpectralBoundaryExact.agda
grep -q 'Nothing from that paper is imported as an Agda proof' \
  DASHI/Physics/YangMills/BalabanP33PhysicalGapScaleInvarianceExact.agda

# Reject the invalid unrestricted rational monotonicity shortcut explicitly.
if grep -R -n 'rationalOrderedScaleAlgebra' "${files[@]}"; then
  echo "round twenty-six reintroduced unrestricted rational multiplication monotonicity" >&2
  exit 1
fi

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound26Validation.agda
