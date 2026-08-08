#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round34.sh

files=(
  DASHI/Physics/YangMills/YangMillsPaperClaimAuditCarrierExact.agda
  DASHI/Physics/YangMills/YangMillsCizekEinsteinCartanClaimAuditExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalPlaquetteFirstVariationExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalCovariantPlaquetteCurlExact.agda
  DASHI/Physics/YangMills/BalabanP33CovariantCurlDefectFactorizationExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundCovariantCurlInstantiationExact.agda
  DASHI/Physics/YangMills/BalabanP33FlatPlaquetteFirstVariationCurlExact.agda
  DASHI/Physics/YangMills/BalabanP33CovariantCurlRadiusStressTestExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound35PlaquetteCurlValidation.agda
)

doc=Docs/support/reference/YangMillsPlaquetteCurlRound35.md
index=Docs/support/reference/YangMillsReferenceIndex.md
workflow=.github/workflows/yang-mills-clay-highest-alpha-round35.yml

for file in "${files[@]}" "$doc" "$index" "$workflow"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round thirty five contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'YangMillsPaperClaimAuditCarrierExact.agda:einsteinCartanYangMillsIsNotDefinitionallyPureYangMills'
  'YangMillsPaperClaimAuditCarrierExact.agda:auxiliaryBoundaryLangevinIsNotSlabTransferKernel'
  'YangMillsPaperClaimAuditCarrierExact.agda:boundarySlabTransferKernelIsNotPhysicalHamiltonian'
  'YangMillsCizekEinsteinCartanClaimAuditExact.agda:monographAssumptionCountExact'
  'YangMillsCizekEinsteinCartanClaimAuditExact.agda:monographBridgeCountExact'
  'YangMillsCizekEinsteinCartanClaimAuditExact.agda:slabAssumptionCountExact'
  'YangMillsCizekEinsteinCartanClaimAuditExact.agda:slabBridgeCountExact'
  'YangMillsCizekEinsteinCartanClaimAuditExact.agda:monographTheoryIsNotDefinitionallyPureYM'
  'YangMillsCizekEinsteinCartanClaimAuditExact.agda:slabKernelIsNotPhysicalHamiltonian'
  'YangMillsCizekEinsteinCartanClaimAuditExact.agda:auxiliarySamplerCannotReplaceSlabKernel'
  'YangMillsCizekEinsteinCartanClaimAuditExact.agda:monographEvidenceIsNotKernelProof'
  'YangMillsCizekEinsteinCartanClaimAuditExact.agda:slabOutcomeRemainsConditional'
  'BalabanP33PhysicalPlaquetteFirstVariationExact.agda:generatedFirstVariationTermsAreFourOrdered'
  'BalabanP33PhysicalPlaquetteFirstVariationExact.agda:plaquetteFirstVariationTermCountExact'
  'BalabanP33PhysicalPlaquetteFirstVariationExact.agda:plaquetteFirstVariationIsFourOrderedSum'
  'BalabanP33PhysicalCovariantPlaquetteCurlExact.agda:rightTrivializedFirstVariationWithNormWeights'
  'BalabanP33PhysicalCovariantPlaquetteCurlExact.agda:weightedCurlAtUnitNormExact'
  'BalabanP33PhysicalCovariantPlaquetteCurlExact.agda:plaquetteProductTimesRightInverseWithNorms'
  'BalabanP33PhysicalCovariantPlaquetteCurlExact.agda:physicalPlaquetteRightInverseExact'
  'BalabanP33PhysicalCovariantPlaquetteCurlExact.agda:physicalPlaquetteFirstVariationIsCovariantCurl'
  'BalabanP33CovariantCurlDefectFactorizationExact.agda:covariantCurlDefectIsAdjointDefectSum'
  'BalabanP33CovariantCurlDefectFactorizationExact.agda:adjointDefectCurlSumFactorizes'
  'BalabanP33CovariantCurlDefectFactorizationExact.agda:physicalCovariantCurlDefectFactorizationExact'
  'BalabanSelectedBackgroundCovariantCurlInstantiationExact.agda:selectedBackgroundFirstVariationIsCovariantCurl'
  'BalabanSelectedBackgroundCovariantCurlInstantiationExact.agda:selectedBackgroundCovariantCurlDefectFactorization'
  'BalabanP33FlatPlaquetteFirstVariationCurlExact.agda:flatFirstVariationIsPureCurl'
  'BalabanP33FlatPlaquetteFirstVariationCurlExact.agda:flatFirstVariationScalarPartZero'
  'BalabanP33FlatPlaquetteFirstVariationCurlExact.agda:physicalIdentityFirstVariationIsFlatCurl'
  'BalabanP33CovariantCurlRadiusStressTestExact.agda:stressTurnUnitNorm'
  'BalabanP33CovariantCurlRadiusStressTestExact.agda:stressTurnInsideConfiguredRadius'
  'BalabanP33CovariantCurlRadiusStressTestExact.agda:flatCancellingCurlExact'
  'BalabanP33CovariantCurlRadiusStressTestExact.agda:stressCovariantCurlNormSqExact'
  'BalabanP33CovariantCurlRadiusStressTestExact.agda:stressBudgetSquarePlusGapIsCurlNormSq'
  'BalabanP33CovariantCurlRadiusStressTestExact.agda:correlatedCurvatureStressConclusion'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:fourFactorSingletonCountExact'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:fourFactorHigherCountExact'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:fourFactorLinearNonlinearExpansionExact'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:fourFactorTelescopeIsLinearPlusNonlinear'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:physicalPlacementWilsonDefectLinearNonlinearExact'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:physicalPlaquetteWilsonDefectLinearNonlinearExact'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:canonicalBoundsAsRound34Control'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:canonicalBoundsImplyWLocal'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:selectedVariationalCanonicalTerminalCoefficient'
  'BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda:selectedVariationalCanonicalOneThirtySecond'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Bibliographic guards.
grep -q '10.5281/zenodo.17246443' \
  DASHI/Physics/YangMills/YangMillsCizekEinsteinCartanClaimAuditExact.agda
grep -q '10.5281/zenodo.17718647' \
  DASHI/Physics/YangMills/YangMillsCizekEinsteinCartanClaimAuditExact.agda
grep -q '10.5281/zenodo.18280110' \
  DASHI/Physics/YangMills/YangMillsCizekEinsteinCartanClaimAuditExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33PhysicalCovariantPlaquetteCurlExact.agda
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33PhysicalPlaquetteFirstVariationExact.agda
grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33CovariantCurlDefectFactorizationExact.agda
grep -q '10.1007/BF01229381' \
  DASHI/Physics/YangMills/BalabanSelectedBackgroundCovariantCurlInstantiationExact.agda
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda

# Exact theory/operator separation, transport-order, partition and adversarial guards.
grep -q 'einsteinCartanYangMillsTheory' \
  DASHI/Physics/YangMills/YangMillsPaperClaimAuditCarrierExact.agda
grep -q 'boundarySlabTransferKernel' \
  DASHI/Physics/YangMills/YangMillsPaperClaimAuditCarrierExact.agda
grep -q 'torsionGravitySectorExactlyDecouplesToPureYM' \
  DASHI/Physics/YangMills/YangMillsCizekEinsteinCartanClaimAuditExact.agda
grep -q 'ultravioletContinuumOnR4ActuallyConstructed' \
  DASHI/Physics/YangMills/YangMillsCizekEinsteinCartanClaimAuditExact.agda
grep -Fq 'Ad_A X0 + Ad_{AB} X1' \
  DASHI/Physics/YangMills/BalabanP33PhysicalCovariantPlaquetteCurlExact.agda
grep -Fq -- '- Ad_{AB} X2 - Ad_{ABC^-1} X3' \
  DASHI/Physics/YangMills/BalabanP33PhysicalCovariantPlaquetteCurlExact.agda
grep -Fq 'Ad_U X - X' \
  DASHI/Physics/YangMills/BalabanP33CovariantCurlDefectFactorizationExact.agda
grep -Fq 'sum_{|S|=1}' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda
grep -q 'four singleton terms and eleven higher-order terms' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda
grep -q 'physicalWilsonCanonicalBoundsLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda
grep -q '67108863 / 67108865' \
  DASHI/Physics/YangMills/BalabanP33CovariantCurlRadiusStressTestExact.agda
grep -q '1073741824 / 4503599761588225' \
  DASHI/Physics/YangMills/BalabanP33CovariantCurlRadiusStressTestExact.agda
grep -q '2589569785603817471 / 10880332700790838158950400' \
  DASHI/Physics/YangMills/BalabanP33CovariantCurlRadiusStressTestExact.agda
grep -q 'selectedEulerLagrangeCorrelationStillRequiredLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33CovariantCurlRadiusStressTestExact.agda
grep -q 'selectedBackgroundCurvatureLowerProducerLevel = conditional' \
  DASHI/Physics/YangMills/BalabanSelectedBackgroundCovariantCurlInstantiationExact.agda

grep -Fq '[Round 35 — literal plaquette differentiation, covariant curl and adversarial stress test](./YangMillsPlaquetteCurlRound35.md)' "$index"
grep -q 'The repeated `Ad_(A B)` is essential' "$doc"
grep -q 'four singleton terms and eleven higher-order terms' "$doc"
grep -q 'Einstein–Cartan–Yang–Mills' "$doc"
grep -q 'A static audit is not a kernel result' "$doc"
grep -q 'variationalEulerLagrangeEquationAtSelectedBackground' "$doc"
grep -q 'groupedSixteenAtomNonlinearRemainderLower' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound35PlaquetteCurlValidation.agda
