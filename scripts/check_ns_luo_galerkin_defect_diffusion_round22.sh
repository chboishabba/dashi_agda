#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_filtered_defect_excursion_round21.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLuoFilteredVorticitySubfilterStressExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteParaproductRangePartitionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinCriticalFilteredEnstrophyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTwoPointCrossDefectDiffusionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPairFrequencyDefectDiffusionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinPairDefectEvolutionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiveSourceDefectCriticalTaxExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBadExcursionHysteresisTaxExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBadAmplitudeBernsteinScalingNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDissipationWavenumberAmplitudeRepairExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDissipationWavenumberSplitExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicLowTransportSkewCancellationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoStrainKernelSphericalMeanZeroExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteFilterIncrementJensenExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteGeometricResidualTailExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCriticalProductionGronwallClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoNestedGalerkinShellLimitExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCriticalRestartContradictionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinDefectDiffusionRound22Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

audit_targets=(
  "${files[@]}"
  docs/ns-luo-galerkin-defect-diffusion-round22.md
)

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${audit_targets[@]}"; then
  echo "round twenty-two contains a hole, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

grep -q 'subfilterStressDivergenceIdentity' DASHI/Physics/Closure/NSTriadKNLuoFilteredVorticitySubfilterStressExact.agda
grep -q 'resolvedFilteredVorticityEquation' DASHI/Physics/Closure/NSTriadKNLuoFilteredVorticitySubfilterStressExact.agda

grep -q 'SupportedTriadRange' DASHI/Physics/Closure/NSTriadKNLuoFiniteParaproductRangePartitionExact.agda
grep -q 'classifyFilteredInteraction' DASHI/Physics/Closure/NSTriadKNLuoFiniteParaproductRangePartitionExact.agda

grep -q 'coordinateFilteredEnstrophyIdentity' DASHI/Physics/Closure/NSTriadKNLuoGalerkinCriticalFilteredEnstrophyExact.agda
grep -q 'weightedGalerkinFilteredEnstrophyIdentity' DASHI/Physics/Closure/NSTriadKNLuoGalerkinCriticalFilteredEnstrophyExact.agda

grep -q 'twoPointDiffusionProductRule' DASHI/Physics/Closure/NSTriadKNLuoTwoPointCrossDefectDiffusionExact.agda
grep -q 'positiveMixedRemainderWitness' DASHI/Physics/Closure/NSTriadKNLuoTwoPointCrossDefectDiffusionExact.agda
grep -q 'negativeMixedRemainderWitness' DASHI/Physics/Closure/NSTriadKNLuoTwoPointCrossDefectDiffusionExact.agda

grep -q 'pairFrequencyShellDamping' DASHI/Physics/Closure/NSTriadKNLuoPairFrequencyDefectDiffusionExact.agda
grep -q 'highHighLowOutputMissesTwoUnits' DASHI/Physics/Closure/NSTriadKNLuoPairFrequencyDefectDiffusionExact.agda

grep -q 'localPairDefectDampedEvolution' DASHI/Physics/Closure/NSTriadKNLuoGalerkinPairDefectEvolutionExact.agda
grep -q 'finiteWeightedPairDefectDampedEvolution' DASHI/Physics/Closure/NSTriadKNLuoGalerkinPairDefectEvolutionExact.agda

grep -q 'fiveSourceCriticalTax' DASHI/Physics/Closure/NSTriadKNLuoFiveSourceDefectCriticalTaxExact.agda
grep -q 'fiveSourceDefectAbsorption' DASHI/Physics/Closure/NSTriadKNLuoFiveSourceDefectCriticalTaxExact.agda

grep -q 'localHysteresisEntryTax' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionHysteresisTaxExact.agda
grep -q 'uniformHysteresisEntryTax' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionHysteresisTaxExact.agda
grep -q 'zeroGapPaysNothing' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionHysteresisTaxExact.agda

grep -q 'bernsteinSupercriticalGapIdentity' DASHI/Physics/Closure/NSTriadKNLuoBadAmplitudeBernsteinScalingNoGoExact.agda
grep -q 'viscousHighModeAmplitudeAbsorption' DASHI/Physics/Closure/NSTriadKNLuoDissipationWavenumberAmplitudeRepairExact.agda
grep -q 'finiteDissipationWavenumberSplit' DASHI/Physics/Closure/NSTriadKNLuoFiniteDissipationWavenumberSplitExact.agda

grep -q 'periodicLowTransportSkewCancellation' DASHI/Physics/Closure/NSTriadKNLuoPeriodicLowTransportSkewCancellationExact.agda
grep -q 'sphericalKernelMeanZero' DASHI/Physics/Closure/NSTriadKNLuoStrainKernelSphericalMeanZeroExact.agda
grep -q 'normalizedFiniteFilterIncrementJensen' DASHI/Physics/Closure/NSTriadKNLuoFiniteFilterIncrementJensenExact.agda
grep -q 'finiteGeometricIdentity' DASHI/Physics/Closure/NSTriadKNLuoFiniteGeometricResidualTailExact.agda
grep -q 'criticalProductionAbsorptionWithGronwallReservoir' DASHI/Physics/Closure/NSTriadKNLuoCriticalProductionGronwallClosureExact.agda
grep -q 'nestedGalerkinShellLimitBelowThreshold' DASHI/Physics/Closure/NSTriadKNLuoNestedGalerkinShellLimitExact.agda
grep -q 'criticalRestartContradictsFiniteMaximality' DASHI/Physics/Closure/NSTriadKNLuoCriticalRestartContradictionExact.agda

grep -q '10.1016/S0065-2687(08)60464-1' DASHI/Physics/Closure/NSTriadKNLuoFilteredVorticitySubfilterStressExact.agda
grep -q '10.1007/s00021-014-0167-4' DASHI/Physics/Closure/NSTriadKNLuoPairFrequencyDefectDiffusionExact.agda
grep -q '10.48550/arXiv.2606.27560' DASHI/Physics/Closure/NSTriadKNLuoGalerkinPairDefectEvolutionExact.agda
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNLuoStrainKernelSphericalMeanZeroExact.agda
grep -q '10.24033/asens.1404' DASHI/Physics/Closure/NSTriadKNLuoFiniteParaproductRangePartitionExact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNLuoGalerkinCriticalFilteredEnstrophyExact.agda
grep -q '10.1007/BF01174182' DASHI/Physics/Closure/NSTriadKNLuoCriticalRestartContradictionExact.agda

grep -q 'actualPeriodicFourierCellsConstructed' DASHI/Physics/Closure/NSTriadKNLuoGalerkinPairDefectEvolutionExact.agda
grep -q 'fiveSourceCriticalTaxProduced' DASHI/Physics/Closure/NSTriadKNLuoGalerkinPairDefectEvolutionExact.agda
grep -q 'navierStokesPositiveVariationBoundProduced' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionHysteresisTaxExact.agda
grep -q 'navierStokesDissipationWavenumberBoundProduced' DASHI/Physics/Closure/NSTriadKNLuoDissipationWavenumberAmplitudeRepairExact.agda
grep -q 'periodicPrincipalValueDistributionConstructed' DASHI/Physics/Closure/NSTriadKNLuoStrainKernelSphericalMeanZeroExact.agda
grep -q 'infiniteCutoffPassageProved' DASHI/Physics/Closure/NSTriadKNLuoCriticalProductionGronwallClosureExact.agda
grep -q 'shellConvergenceProducedAnalytically' DASHI/Physics/Closure/NSTriadKNLuoNestedGalerkinShellLimitExact.agda
grep -q 'fujitaKatoRestartProduced' DASHI/Physics/Closure/NSTriadKNLuoCriticalRestartContradictionExact.agda

test -f docs/ns-luo-galerkin-defect-diffusion-round22.md

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinDefectDiffusionRound22Validation.agda
