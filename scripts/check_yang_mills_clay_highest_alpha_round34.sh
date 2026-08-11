#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round33.sh

files=(
  DASHI/Physics/YangMills/BalabanP33RelaxedRadiusPrincipalChartExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalLinearRemainderWLocalExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound34PhysicalRadiusWLocalValidation.agda
)

doc=Docs/support/reference/YangMillsPhysicalRadiusWLocalRound34.md
index=Docs/support/reference/YangMillsReferenceIndex.md
workflow=.github/workflows/yang-mills-clay-highest-alpha-round34.yml

for file in "${files[@]}" "$doc" "$index" "$workflow"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round thirty four contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'BalabanP33RelaxedRadiusPrincipalChartExact.agda:unitInverseDefectExpansion'
  'BalabanP33RelaxedRadiusPrincipalChartExact.agda:inverseLinkDefectSqExact'
  'BalabanP33RelaxedRadiusPrincipalChartExact.agda:configuredScalarFloorPositive'
  'BalabanP33RelaxedRadiusPrincipalChartExact.agda:relaxedRadiusImpliesScalarFloor'
  'BalabanP33RelaxedRadiusPrincipalChartExact.agda:relaxedRadiusImpliesPositiveScalarPart'
  'BalabanP33RelaxedRadiusPrincipalChartExact.agda:relaxedRadiusImpliesPrincipalImage'
  'BalabanP33RelaxedRadiusPrincipalChartExact.agda:relaxedRadiusPhysicalInverseLogOrientation'
  'BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda:selectedBackgroundDefectBelowPublishedUpper'
  'BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda:selectedBackgroundRelaxedInverseLinkRadius'
  'BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda:selectedBackgroundPhysicalLinkPrincipalImage'
  'BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda:selectedBridgeChartAdmissionIsOnPhysicalLink'
  'BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda:selectedBackgroundPhysicalInverseLogOrientation'
  'BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda:selectedVariationalRadiusAt'
  'BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda:selectedVariationalTerminalCoefficient'
  'BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda:selectedVariationalOneThirtySecond'
  'BalabanP33PhysicalLinearRemainderWLocalExact.agda:physicalCorrelationInputsAt'
  'BalabanP33PhysicalLinearRemainderWLocalExact.agda:physicalLinearRemainderControlImpliesWLocal'
  'BalabanP33PhysicalLinearRemainderWLocalExact.agda:selectedVariationalCorrelationTerminalCoefficient'
  'BalabanP33PhysicalLinearRemainderWLocalExact.agda:selectedVariationalCorrelationOneThirtySecond'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Bibliographic guards.
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33RelaxedRadiusPrincipalChartExact.agda
grep -q '10.1007/BF01229381' \
  DASHI/Physics/YangMills/BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda
grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33PhysicalLinearRemainderWLocalExact.agda
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33PhysicalLinearRemainderWLocalExact.agda

# Scope and exact-constant guards.
grep -Fq 'N(U^-1 - 1) = 2 (1 - q0(U))' \
  DASHI/Physics/YangMills/BalabanP33RelaxedRadiusPrincipalChartExact.agda
grep -Fq '1 - 2 rho^2 <= q0(U)' \
  DASHI/Physics/YangMills/BalabanP33RelaxedRadiusPrincipalChartExact.agda
grep -q 'publishedUpperBelowRelaxedRadius' \
  DASHI/Physics/YangMills/BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda
grep -q 'rhoOverThirtySix' \
  DASHI/Physics/YangMills/BalabanP33PhysicalLinearRemainderWLocalExact.agda
grep -q 'rhoOverOneFortyFour' \
  DASHI/Physics/YangMills/BalabanP33PhysicalLinearRemainderWLocalExact.agda
grep -q '10739/196608' \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound34PhysicalRadiusWLocalValidation.agda

grep -Fq '[Round 34 — physical selected-background radius and W-local assembly](./YangMillsPhysicalRadiusWLocalRound34.md)' "$index"
grep -q 'The radius premise and W-local record are no longer independent' "$doc"
grep -q 'A static audit is not a kernel result' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound34PhysicalRadiusWLocalValidation.agda
