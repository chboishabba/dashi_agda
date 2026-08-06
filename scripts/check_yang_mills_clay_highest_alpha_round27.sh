#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round26.sh

files=(
  DASHI/Physics/YangMills/BalabanP33WilsonAtomSignedPerturbationExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonIncidenceExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonSignedGlobalExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonLocalToSharpDefectExact.agda
  DASHI/Physics/YangMills/BalabanP33PeriodicDivergenceUpperExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeSignedLowerExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalBackgroundGaugeResidualExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33SelectedBackgroundFiniteCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33CubicShellSeriesExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalInfiniteDiscountedLossExact.agda
  DASHI/Physics/YangMills/BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound27Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done
test -f .github/workflows/yang-mills-clay-highest-alpha-round27.yml

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round twenty-seven contains a hole, imported receipt, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33WilsonAtomSignedPerturbationExact.agda:weightedYoungLower'
  'BalabanP33WilsonAtomSignedPerturbationExact.agda:bilinearPerturbationSignedLower'
  'BalabanP33PhysicalWilsonIncidenceExact.agda:physicalWilsonDiagonalIncidenceExact'
  'BalabanP33PhysicalWilsonIncidenceExact.agda:physicalWilsonCrossIncidenceExact'
  'BalabanP33PhysicalWilsonSignedGlobalExact.agda:physicalWilsonSignedGlobalThirteenTwentyFourths'
  'BalabanP33PhysicalWilsonLocalToSharpDefectExact.agda:samePhysicalPerturbationWLocalImpliesSharpDefect'
  'BalabanP33PeriodicDivergenceUpperExact.agda:physicalPeriodicDivergenceUpper'
  'BalabanP33PhysicalBackgroundGaugeSignedLowerExact.agda:flatGaugeEnergyIsPhysicalDivergence'
  'BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda:backgroundGaugeResidualSignedLowerSixtyFourRelaxed'
  'BalabanP33PhysicalBackgroundGaugeResidualExact.agda:backgroundGaugeResidualSignedLowerSixtyFour'
  'BalabanP33PhysicalTerminalHessianCoercivityExact.agda:literalHessianCoerciveAtTerminalCoefficient'
  'BalabanP33PhysicalTerminalHessianCoercivityExact.agda:literalHessianCoerciveAtOneThirtySecond'
  'BalabanP33SelectedBackgroundFiniteCoercivityExact.agda:selectedGaugeFirstLower'
  'BalabanP33SelectedBackgroundFiniteCoercivityExact.agda:selectedWilsonLower'
  'BalabanP33SelectedBackgroundFiniteCoercivityExact.agda:selectedBackgroundLiteralHessianTerminalCoefficient'
  'BalabanP33SelectedBackgroundFiniteCoercivityExact.agda:selectedBackgroundLiteralHessianOneThirtySecond'
  'BalabanP33CubicShellSeriesExact.agda:cubicShellFiniteClosedForm'
  'BalabanP33CubicShellSeriesExact.agda:finiteErrorAgainstClosedForm'
  'BalabanP33PhysicalInfiniteDiscountedLossExact.agda:discountedGeometricLossClosedForm'
  'BalabanP33PhysicalInfiniteDiscountedLossExact.agda:discountedLossTailExact'
  'BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda:counterSatisfiesRelaxedInverseLinkRadius'
  'BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda:counterWilsonDefectExact'
  'BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda:counterWLocalViolationGapPositive'
)
for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Bibliographic/source guards.
grep -q '10.1103/PhysRevD.10.2445' DASHI/Physics/YangMills/BalabanP33WilsonAtomSignedPerturbationExact.agda
grep -q '10.1007/BF01240355' DASHI/Physics/YangMills/BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda
grep -q '10.1007/BF01211042' DASHI/Physics/YangMills/BalabanP33PhysicalWilsonIncidenceExact.agda
grep -q '10.1007/BF01466594' DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
grep -q '10.1007/BF01229381' DASHI/Physics/YangMills/BalabanP33SelectedBackgroundFiniteCoercivityExact.agda
grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
grep -q '10.1007/BF01240221' DASHI/Physics/YangMills/BalabanP33CubicShellSeriesExact.agda
grep -q 'math-ph/0505008' DASHI/Physics/YangMills/BalabanP33CubicShellSeriesExact.agda
grep -q '10.1007/s00023-013-0303-3' DASHI/Physics/YangMills/BalabanP33PhysicalInfiniteDiscountedLossExact.agda

# Scope and anti-conflation guards.
grep -q 'cubicShellInfiniteLimitProducerLevel = conditional' DASHI/Physics/YangMills/BalabanP33CubicShellSeriesExact.agda
grep -q 'physicalGeometricLossProducerLevel = conditional' DASHI/Physics/YangMills/BalabanP33PhysicalInfiniteDiscountedLossExact.agda
for file in \
  BalabanP33PeriodicDivergenceUpperExact.agda \
  BalabanP33PhysicalBackgroundGaugeSignedLowerExact.agda \
  BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact.agda \
  BalabanP33PhysicalBackgroundGaugeResidualExact.agda; do
  grep -q 'Bridge.asPeriodicField' "DASHI/Physics/YangMills/$file"
done
grep -q 'sum_p q_p(h) = 6' DASHI/Physics/YangMills/BalabanP33PhysicalWilsonIncidenceExact.agda
grep -q 'sum_p C_p(h) = 18' DASHI/Physics/YangMills/BalabanP33PhysicalWilsonIncidenceExact.agda
grep -q '10739/196608' DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
grep -q '4595/196608' DASHI/Physics/YangMills/BalabanP33PhysicalTerminalHessianCoercivityExact.agda
grep -q 'single perturbation object' DASHI/Physics/YangMills/BalabanP33SelectedBackgroundFiniteCoercivityExact.agda
grep -q '35167404019/158329674989568' DASHI/Physics/YangMills/BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda
grep -q 'A2 cannot be discharged from A1 alone' DASHI/Physics/YangMills/BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound27Validation.agda
