#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_physical_carrier_partition_round28.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLuoUniformCommutatorTaxRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEnergyContinuationRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNDependentPhysicalODECarrierRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNFiniteGalerkinVectorLipschitzRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNFiniteFlowBlowupAlternativeRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNGlobalBilinearShellPairingRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNDelayedPositivePartRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNDiscreteMultiplierTelescopingRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNSignedCrossShellAlmostOrthogonalityRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNScaleNormalisedAmplitudeAuditRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadFeasibilityRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNAffineOwnerCostOptimizationRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNBoundaryVanishingClassificationRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNCriticalCompactnessSerrinRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaRound29Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDependentFlowOwnerAnalysisRound29Validation.agda
  DASHI/Papers/NavierStokes/DependentFlowOwnerAnalysisRound29.agda
  DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound29.agda
)

docs=(
  docs/ns-clay-contract/README.md
  docs/ns-clay-contract/architecture.puml
  docs/ns-clay-contract/dependent-flow-owner-analysis-round29.md
  docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
)

workflow=.github/workflows/ns-luo-dependent-flow-owner-analysis-round29.yml

for file in "${files[@]}" "${docs[@]}" "$workflow"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${files[@]}" "${docs[@]}"; then
  echo "round twenty-nine contains a hole, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

selector=DASHI/Physics/Closure/NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact.agda
grep -q '10.1007/BF02547354' "$selector"
grep -q '10.1090/chel/343' "$selector"
grep -q 'reconstructedNegativeCoefficientTransverse' "$selector"
grep -q 'positiveCoefficientLerayFixed' "$selector"
grep -q 'negativeCoefficientLerayFixed' "$selector"
grep -q 'reconstructedPhysicalSelectors' "$selector"
grep -q 'reconstructedPhysicalStateSelectorInstantiated = true' "$selector"
grep -q 'literalCoefficientLerayFixingClosed = true' "$selector"
grep -q 'fullGalerkinVectorFieldMapsReconstructedState = false' "$selector"

dependent=DASHI/Physics/Closure/NSTriadKNDependentPhysicalODECarrierRound29Exact.agda
grep -q 'SelectorEquivariantVectorField' "$dependent"
grep -q 'physicalVectorField' "$dependent"
grep -q 'outputIsPhysicalSelectorFixed' "$dependent"
grep -q 'DependentPhysicalTrajectory' "$dependent"
grep -q 'literalNavierStokesVectorFieldEquivarianceClosed = false' "$dependent"

vector_lipschitz=DASHI/Physics/Closure/NSTriadKNFiniteGalerkinVectorLipschitzRound29Exact.agda
grep -q '10.1090/chel/343' "$vector_lipschitz"
grep -q 'finiteVectorDifferenceL1' "$vector_lipschitz"
grep -q 'finiteVectorLipschitzWeight' "$vector_lipschitz"
grep -q 'finiteGalerkinVectorLocalLipschitz' "$vector_lipschitz"
grep -q 'finiteRationalVectorLocalLipschitzClosed = true' "$vector_lipschitz"
grep -q 'continuumRealCoordinateEquivalenceClosed = false' "$vector_lipschitz"

flow=DASHI/Physics/Closure/NSTriadKNFiniteFlowBlowupAlternativeRound29Exact.agda
grep -q 'EscapeWitness' "$flow"
grep -q 'uniformBoundContradictsEscape' "$flow"
grep -q 'energyConstructsUniformNormBound' "$flow"
grep -q 'energyExcludesFiniteMaximalTime' "$flow"
grep -q 'literalFinitePicardLindelofInstantiated = false' "$flow"

pairing=DASHI/Physics/Closure/NSTriadKNGlobalBilinearShellPairingRound29Exact.agda
grep -q 'globalPairingFiveSourceIdentity' "$pairing"
grep -q 'physicalShellBalanceExpandsOnce' "$pairing"
grep -q 'physicalTimeDependentShellBalanceInstantiated = false' "$pairing"

positive=DASHI/Physics/Closure/NSTriadKNDelayedPositivePartRound29Exact.agda
grep -q 'oppositePairCancelsBeforeMagnitude' "$positive"
grep -q 'delayedPositivePartBelowAtomwiseFallback' "$positive"
grep -q 'groupedTaxBelowLossyFallback' "$positive"

multiplier=DASHI/Physics/Closure/NSTriadKNDiscreteMultiplierTelescopingRound29Exact.agda
grep -q '10.1002/cpa.3160410704' "$multiplier"
grep -q 'multiplierDifferenceIsSignedPathSum' "$multiplier"
grep -q 'multiplierEndpointMagnitudeBound' "$multiplier"

uniform=DASHI/Physics/Closure/NSTriadKNLuoUniformCommutatorTaxRound27Exact.agda
grep -q 'cutoffIndependentCommutatorCellCoefficient' "$uniform"
grep -q 'finiteCutoffIndependentCommutatorTax' "$uniform"

cross=DASHI/Physics/Closure/NSTriadKNSignedCrossShellAlmostOrthogonalityRound29Exact.agda
grep -q 'SignedCrossShellCell' "$cross"
grep -q 'crossShellSignedAggregation' "$cross"
grep -q 'finiteAlmostOrthogonalityBound' "$cross"
grep -q 'cutoffUniformOperatorCotlarSteinClosed = false' "$cross"

amplitude=DASHI/Physics/Closure/NSTriadKNScaleNormalisedAmplitudeAuditRound29Exact.agda
grep -q 'oneInverseScaleRepairsHomogeneity' "$amplitude"
grep -q 'candidateHasCriticalHomogeneity' "$amplitude"
grep -q 'physicalBadAmplitudeSquareBudgetClosed = false' "$amplitude"

hhbad=DASHI/Physics/Closure/NSTriadKNHHBadFeasibilityRound29Exact.agda
grep -q '10.1512/iumj.1993.42.42034' "$hhbad"
grep -q 'unavoidableFloorRefutesCurrentHHBadFamily' "$hhbad"
grep -q 'HHBadParameterCandidate' "$hhbad"
grep -q 'physicalHHBadParameterTupleConstructed = false' "$hhbad"

costs=DASHI/Physics/Closure/NSTriadKNAffineOwnerCostOptimizationRound29Exact.agda
grep -q 'AffineEtaParameter' "$costs"
grep -q 'SymbolicOwnerCost' "$costs"
grep -q 'symbolicBudgetProducesStrictAdmissibleBudget' "$costs"
grep -q 'physicalSymbolicOwnerCostsInstantiated = false' "$costs"

boundary=DASHI/Physics/Closure/NSTriadKNBoundaryVanishingClassificationRound29Exact.agda
grep -q 'BoundaryVanishingReason' "$boundary"
grep -q 'boundaryReasonPartitionExact' "$boundary"
grep -q 'classifiedBoundaryTotalVanishes' "$boundary"
grep -q 'physicalBoundarySubtypeLimitsClosed = false' "$boundary"

serrin=DASHI/Physics/Closure/NSTriadKNCriticalCompactnessSerrinRound29Exact.agda
grep -q '10.1007/BF02392477' "$serrin"
grep -q '10.1007/BF00281418' "$serrin"
grep -q 'timeDerivativeBoundFromEquation' "$serrin"
grep -q 'criticalToSerrinQuantitative' "$serrin"
grep -q 'serrinExponentIdentity' "$serrin"
grep -q 'criticalAubinLionsInstantiated = false' "$serrin"

integration=DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaRound29Exact.agda
grep -q 'Round29ExactEvidence' "$integration"
grep -q 'hhBadUnavoidableFloorNoGo' "$integration"
grep -q 'symbolicBudgetPromotion' "$integration"
grep -q 'quantitativeCriticalToSerrin' "$integration"
grep -q 'physicalFlowStillOpen' "$integration"
grep -q 'strictMarginStillOpen' "$integration"
grep -q 'clayPromotionStillFalse' "$integration"

paper=DASHI/Papers/NavierStokes/DependentFlowOwnerAnalysisRound29.agda
grep -q 'canonicalDependentFlowOwnerAnalysisRound29Status' "$paper"
grep -q 'finiteGlobalFlowStillOpen' "$paper"
grep -q 'physicalTaxesStillOpen' "$paper"
grep -q 'clayPromotionStillFalse' "$paper"

current=DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound29.agda
grep -q 'canonicalCurrentNSPaperTheoremInterfaceRound29' "$current"
grep -q 'uniformOperatorTaxStillOpen' "$current"
grep -q 'physicalOwnerTaxesStillOpen' "$current"
grep -q 'currentRound29ClayPromotionFalse' "$current"

grep -q '\[Round 29 dependent flow and owner analysis\](dependent-flow-owner-analysis-round29.md)' docs/ns-clay-contract/README.md
grep -q '\[Back to the Clay-contract overview\](README.md)' docs/ns-clay-contract/dependent-flow-owner-analysis-round29.md
grep -q 'Round 29' docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
grep -q 'Dependent physical ODE carrier' docs/ns-clay-contract/architecture.puml

grep -q 'agent/ns-luo-dependent-flow-and-owner-analysis-round29' "$workflow"
grep -q 'check_ns_luo_dependent_flow_owner_analysis_round29.sh' "$workflow"
grep -q 'ns-round29-dependent-flow-owner-analysis-agda' "$workflow"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoDependentFlowOwnerAnalysisRound29Validation.agda
