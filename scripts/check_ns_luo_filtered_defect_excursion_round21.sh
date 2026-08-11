#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_nemgro_physical_audit_round20.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFilteredDirectionContractionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFilteredPairwiseDefectFiniteExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFilteredEnstrophySurplusExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBadExcursionResidenceTaxExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBadExcursionYoungAbsorptionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoThreeLaneCriticalClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDyadicFilteredVorticityLedgerExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoYuResidualBasisComparisonExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCrossProductDefectEvolutionAlgebraExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFilteredDefectExcursionRound21Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

audit_targets=(
  "${files[@]}"
  docs/ns-luo-filtered-defect-excursion-round21.md
)

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${audit_targets[@]}"; then
  echo "round twenty-one contains a hole, postulate, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

grep -q 'exactAmplitudeDirectionDecomposition' DASHI/Physics/Closure/NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact.agda
grep -q 'magnitudeWeightedDirectionIncrementBound' DASHI/Physics/Closure/NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact.agda

grep -q 'sharpContractionIdentity' DASHI/Physics/Closure/NSTriadKNLuoFilteredDirectionContractionExact.agda
grep -q 'filteredDirectionContractionSquaredBound' DASHI/Physics/Closure/NSTriadKNLuoFilteredDirectionContractionExact.agda

grep -q 'finitePairwiseDefectBelowIncrementEnvelope' DASHI/Physics/Closure/NSTriadKNLuoFilteredPairwiseDefectFiniteExact.agda
grep -q 'finiteFilteredNearFieldCoercivity' DASHI/Physics/Closure/NSTriadKNLuoFilteredPairwiseDefectFiniteExact.agda

grep -q 'filteredEnstrophySurplusBound' DASHI/Physics/Closure/NSTriadKNLuoFilteredEnstrophySurplusExact.agda
grep -q 'finiteWeightedFilteredSurplus' DASHI/Physics/Closure/NSTriadKNLuoFilteredEnstrophySurplusExact.agda

grep -q 'localBadExcursionResidenceTax' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionResidenceTaxExact.agda
grep -q 'badResidenceWithCrossingBudget' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionResidenceTaxExact.agda

grep -q 'scaledYoungIdentity' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionYoungAbsorptionExact.agda
grep -q 'badExcursionAmplitudeAbsorption' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionYoungAbsorptionExact.agda

grep -q 'threeLaneAbsorption' DASHI/Physics/Closure/NSTriadKNLuoThreeLaneCriticalClosureExact.agda
grep -q 'strictFiniteCriticalEstimate' DASHI/Physics/Closure/NSTriadKNLuoThreeLaneCriticalClosureExact.agda

grep -q 'weightedSourceDecomposition' DASHI/Physics/Closure/NSTriadKNLuoDyadicFilteredVorticityLedgerExact.agda
grep -q 'finiteCriticalFilteredEnstrophyLedger' DASHI/Physics/Closure/NSTriadKNLuoDyadicFilteredVorticityLedgerExact.agda

grep -q 'sevenEqualsYuPlusPressure' DASHI/Physics/Closure/NSTriadKNLuoYuResidualBasisComparisonExact.agda
grep -q 'pressureFreeSevenEqualsYu' DASHI/Physics/Closure/NSTriadKNLuoYuResidualBasisComparisonExact.agda

grep -q 'kernelTraceFree' DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact.agda
grep -q 'kernelEven' DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact.agda
grep -q 'coordinateAngularCancellation' DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact.agda

grep -q 'crossPerturbationExpansion' DASHI/Physics/Closure/NSTriadKNLuoCrossProductDefectEvolutionAlgebraExact.agda
grep -q 'crossDefectPerturbationExpansion' DASHI/Physics/Closure/NSTriadKNLuoCrossProductDefectEvolutionAlgebraExact.agda
grep -q 'fiveSourceDefectEvolutionSplit' DASHI/Physics/Closure/NSTriadKNLuoCrossProductDefectEvolutionAlgebraExact.agda

grep -q '10.48550/arXiv.2606.27560' DASHI/Physics/Closure/NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact.agda
grep -q '10.48550/arXiv.2606.25341' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionResidenceTaxExact.agda
grep -q '10.48550/arXiv.2606.12756' DASHI/Physics/Closure/NSTriadKNLuoYuResidualBasisComparisonExact.agda
grep -q '10.48550/arXiv.2606.13887' DASHI/Physics/Closure/NSTriadKNLuoYuResidualBasisComparisonExact.agda
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact.agda
grep -q '10.24033/asens.1404' DASHI/Physics/Closure/NSTriadKNLuoDyadicFilteredVorticityLedgerExact.agda

grep -q 'continuumDifferenceQuotientEstimateProved' DASHI/Physics/Closure/NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact.agda
grep -q 'unweightedFarFieldCarlesonClosureProved' DASHI/Physics/Closure/NSTriadKNLuoFilteredEnstrophySurplusExact.agda
grep -q 'navierStokesCrossingBudgetProduced' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionResidenceTaxExact.agda
grep -q 'physicalAmplitudeSquareBudgetProduced' DASHI/Physics/Closure/NSTriadKNLuoBadExcursionYoungAbsorptionExact.agda
grep -q 'periodicPrincipalValueKernelConstructed' DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact.agda
grep -q 'dissipativeDefectInequalityProved' DASHI/Physics/Closure/NSTriadKNLuoCrossProductDefectEvolutionAlgebraExact.agda

test -f docs/ns-luo-filtered-defect-excursion-round21.md

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoFilteredDefectExcursionRound21Validation.agda
