#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

# Validate the complete stacked predecessor first.
bash scripts/check_yang_mills_clay_highest_alpha_round26.sh

files=(
  DASHI/Physics/YangMills/BalabanP33WilsonAtomSignedPerturbationExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonIncidenceExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonSignedGlobalExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonLocalToSharpDefectExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33CubicShellSeriesExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalInfiniteDiscountedLossExact.agda
  DASHI/Physics/YangMills/BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound27Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

test -f .github/workflows/yang-mills-clay-highest-alpha-round27.yml

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round twenty-seven contains a hole, imported receipt, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33WilsonAtomSignedPerturbationExact.agda:weightedYoungLower'
  'BalabanP33WilsonAtomSignedPerturbationExact.agda:bilinearPerturbationExact'
  'BalabanP33WilsonAtomSignedPerturbationExact.agda:bilinearPerturbationSignedLower'
  'BalabanP33PhysicalWilsonIncidenceExact.agda:plaquetteCrossChargeIsThreeDiagonal'
  'BalabanP33PhysicalWilsonIncidenceExact.agda:physicalWilsonDiagonalIncidenceExact'
  'BalabanP33PhysicalWilsonIncidenceExact.agda:physicalWilsonCrossIncidenceExact'
  'BalabanP33PhysicalWilsonSignedGlobalExact.agda:physicalWilsonSignedGlobalBeforeIncidence'
  'BalabanP33PhysicalWilsonSignedGlobalExact.agda:physicalWilsonGlobalCoefficientExact'
  'BalabanP33PhysicalWilsonSignedGlobalExact.agda:physicalWilsonSignedGlobalThirteenTwentyFourths'
  'BalabanP33PhysicalWilsonLocalToSharpDefectExact.agda:sharpWilsonCoefficientFromRho'
  'BalabanP33PhysicalWilsonLocalToSharpDefectExact.agda:physicalWilsonDefectIsBackgroundMinusFlat'
  'BalabanP33PhysicalWilsonLocalToSharpDefectExact.agda:physicalWilsonLocalImpliesSharpDefect'
  'BalabanP33PhysicalWilsonLocalToSharpDefectExact.agda:samePhysicalPerturbationWLocalImpliesSharpDefect'
  'BalabanP33PhysicalTerminalHessianCoercivityExact.agda:terminalPhysicalCoefficientExact'
  'BalabanP33PhysicalTerminalHessianCoercivityExact.agda:terminalCoefficientSplitsAtOneThirtySecond'
  'BalabanP33PhysicalTerminalHessianCoercivityExact.agda:literalHessianCoerciveAtTerminalCoefficient'
  'BalabanP33PhysicalTerminalHessianCoercivityExact.agda:literalHessianCoerciveAtOneThirtySecond'
  'BalabanP33CubicShellSeriesExact.agda:cubicShellTailRecurrence'
  'BalabanP33CubicShellSeriesExact.agda:cubicShellFiniteClosedForm'
  'BalabanP33CubicShellSeriesExact.agda:finiteErrorAgainstClosedForm'
  'BalabanP33PhysicalInfiniteDiscountedLossExact.agda:geometricPartialSumClosedForm'
  'BalabanP33PhysicalInfiniteDiscountedLossExact.agda:discountedGeometricLossClosedForm'
  'BalabanP33PhysicalInfiniteDiscountedLossExact.agda:discountedLossTailExact'
  'BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda:counterInverseLinkDefectSqExact'
  'BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda:counterSatisfiesRelaxedInverseLinkRadius'
  'BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda:counterWilsonDefectExact'
  'BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda:counterWLocalViolationGapExact'
  'BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda:counterWLocalViolationGapPositive'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Primary-source metadata.
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33WilsonAtomSignedPerturbationExact.agda
grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda
grep -q '10.1007/BF01211042' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonIncidenceExact.agda
grep -q '10.1007/BF01466594' \
  DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
grep -q '10.1017/CBO9781139020411' \
  DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
grep -q '10.1007/BF01240221' \
  DASHI/Physics/YangMills/BalabanP33CubicShellSeriesExact.agda
grep -q 'math-ph/0505008' \
  DASHI/Physics/YangMills/BalabanP33CubicShellSeriesExact.agda
grep -q '10.1007/s00023-013-0303-3' \
  DASHI/Physics/YangMills/BalabanP33PhysicalInfiniteDiscountedLossExact.agda

# Scope guards: closed algebra is distinguished from open physical producers.
grep -q 'cubicShellInfiniteLimitProducerLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33CubicShellSeriesExact.agda
grep -q 'physicalGeometricLossProducerLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalInfiniteDiscountedLossExact.agda

grep -q 'sum_p q_p(h) = 6' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonIncidenceExact.agda
grep -q 'sum_p C_p(h) = 18' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonIncidenceExact.agda
grep -q '10739/196608' \
  DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
grep -q '4595/196608' \
  DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
grep -q '35167404019/158329674989568' \
  DASHI/Physics/YangMills/BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda
grep -q 'A2 cannot be discharged from A1 alone' \
  DASHI/Physics/YangMills/BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound27Validation.agda
