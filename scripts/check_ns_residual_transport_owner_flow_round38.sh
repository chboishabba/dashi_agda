#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

bash scripts/check_ns_pq_stabilizer_signed_ledger_round37.sh

files=(
  DASHI/Physics/Closure/NSTriadKNVorticityLineResidualRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNVorticityLineOrthogonalResidualRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNFinitePVDetailOperatorRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNPeriodicPVZeroMassFourierCriterionRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNComZ2GradingRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadRestrictedDissipationRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadOccupationCrossingRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationFlowRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitFibreRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.agda
  DASHI/Physics/Closure/NSTriadKNResidualTransportOwnerFlowRound38Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
  if grep -En '(^|[[:space:]])(postulate|primitive)[[:space:]]|\{!!\}|\?|trustMe|unsafe|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|funext|Properties\.WithK|unique⇒irrelevant|--with-K' "$file"; then
    echo "forbidden proof escape in $file" >&2
    exit 1
  fi
done

# HH-good residual, physical threshold gain and PV detail mathematics.
grep -q 'lineResidualIgnoresParallelComponent' DASHI/Physics/Closure/NSTriadKNVorticityLineResidualRound38Exact.agda
grep -q 'stretchingDescendsToSourceLineQuotient' DASHI/Physics/Closure/NSTriadKNVorticityLineResidualRound38Exact.agda
grep -q 'lineResidualNormSquaredExact' DASHI/Physics/Closure/NSTriadKNVorticityLineOrthogonalResidualRound38Exact.agda
grep -q 'stretchingSquareControlledByLineDetail' DASHI/Physics/Closure/NSTriadKNVorticityLineOrthogonalResidualRound38Exact.agda
grep -q 'stretchingSquarePhysicalDirectionalDefect' DASHI/Physics/Closure/NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact.agda
grep -q 'goodPhysicalStretchingThresholdBound' DASHI/Physics/Closure/NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact.agda
grep -q 'zeroMassKernelAnnihilatesConstantProjector' DASHI/Physics/Closure/NSTriadKNFinitePVDetailOperatorRound38Exact.agda
grep -q 'kernelFactorsThroughProjectorDetail' DASHI/Physics/Closure/NSTriadKNFinitePVDetailOperatorRound38Exact.agda
grep -q 'zeroModeMultiplierForcesKernelMassZero' DASHI/Physics/Closure/NSTriadKNPeriodicPVZeroMassFourierCriterionRound38Exact.agda
grep -q 'periodicStrainKernelMassZeroFromFourierCriterion' DASHI/Physics/Closure/NSTriadKNPeriodicPVZeroMassFourierCriterionRound38Exact.agda

# Com grading.
grep -q 'gradingInvolution' DASHI/Physics/Closure/NSTriadKNComZ2GradingRound38Exact.agda
grep -q 'transportEvenOddDecomposition' DASHI/Physics/Closure/NSTriadKNComZ2GradingRound38Exact.agda
grep -q 'gradingCommutatorIsTwicePCommutator' DASHI/Physics/Closure/NSTriadKNComZ2GradingRound38Exact.agda
grep -q 'oddTransportCarriesFullCommutator' DASHI/Physics/Closure/NSTriadKNComZ2GradingRound38Exact.agda

# HH-bad restricted allocation and two-coordinate control.
grep -q 'sumMaskedViscousChargeFactorizes' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedDissipationRound38Exact.agda
grep -q 'restrictedBadViscosityDominatesNormalizedRate' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedDissipationRound38Exact.agda
grep -q 'restrictedBadViscosityProducesInverseShellCharging' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedDissipationRound38Exact.agda
grep -q 'occupationThresholdCostBound' DASHI/Physics/Closure/NSTriadKNHHBadOccupationCrossingRound38Exact.agda
grep -q 'twoCoordinateBadRegionControl' DASHI/Physics/Closure/NSTriadKNHHBadOccupationCrossingRound38Exact.agda

# Signed pre-tax flow and F4 orbit/incidence mathematics.
grep -q 'cancellationFlowConservesSignedTotal' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationFlowRound38Exact.agda
grep -q 'positiveTaxDecreaseExact' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationFlowRound38Exact.agda
grep -q 'physicalCancellationEdgeTaxSavingExact' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationFlowRound38Exact.agda
grep -q 'pEnergyLegPreservesCutoff' DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitFibreRound38Exact.agda
grep -q 'qEnergyLegPreservesCutoff' DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitFibreRound38Exact.agda
grep -q 'finiteFibrePushforward' DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitFibreRound38Exact.agda
grep -q 'pEnergyLegEnumerationPermutation' DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.agda
grep -q 'qEnergyLegEnumerationPermutation' DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.agda
grep -q 'swapTriadEnumerationPermutation' DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.agda
grep -q 'literalThreeLegFoldIsSixOrderedFold' DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.agda
grep -q 'literalOrderedGalerkinIncidencePowerZero' DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.agda

# Source metadata on load-bearing modules.
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNVorticityLineResidualRound38Exact.agda
grep -q '10.1080/03605309608821197' DASHI/Physics/Closure/NSTriadKNVorticityLineOrthogonalResidualRound38Exact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact.agda
grep -q '10.1007/BF02099744' DASHI/Physics/Closure/NSTriadKNFinitePVDetailOperatorRound38Exact.agda
grep -q '10.1007/978-3-642-16830-7' DASHI/Physics/Closure/NSTriadKNPeriodicPVZeroMassFourierCriterionRound38Exact.agda
grep -q '10.1002/cpa.3160410704' DASHI/Physics/Closure/NSTriadKNComZ2GradingRound38Exact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedDissipationRound38Exact.agda
grep -q '10.1007/BF02547354' DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitFibreRound38Exact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitFibreRound38Exact.agda
grep -q '10.1007/BF02547354' DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.agda

# Keep every still-physical analytic producer fail-closed.
grep -q 'periodicPVHHGoodOwnerEstimateConstructed = false' DASHI/Physics/Closure/NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact.agda
grep -q 'literalPeriodicPVDetailFactorizationConstructed = false' DASHI/Physics/Closure/NSTriadKNFinitePVDetailOperatorRound38Exact.agda
grep -q 'literalPhysicalStrainKernelCharacterRealizationConstructed = false' DASHI/Physics/Closure/NSTriadKNPeriodicPVZeroMassFourierCriterionRound38Exact.agda
grep -q 'physicalOddTransportGramRealizationConstructed = false' DASHI/Physics/Closure/NSTriadKNComZ2GradingRound38Exact.agda
grep -q 'physicalHHBadTrajectoryMaskIdentified = false' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedDissipationRound38Exact.agda
grep -q 'physicalHHBadRestrictedGainEstimateConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedDissipationRound38Exact.agda
grep -q 'physicalHHBadIntegratedDefectBoundConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadOccupationCrossingRound38Exact.agda
grep -q 'physicalHHBadPositiveVariationBoundConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadOccupationCrossingRound38Exact.agda
grep -q 'physicalNineOwnerCancellationNetworkConstructed = false' DASHI/Physics/Closure/NSTriadKNSignedOwnerCancellationFlowRound38Exact.agda
grep -q 'literalGalerkinOrbitFibrePartitionConstructed = false' DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitFibreRound38Exact.agda
grep -q 'literalConvectionPairingEqualsOrderedIncidenceFoldConstructed = false' DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.agda

chmod +x scripts/agda29_without_k_wrapper.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI.Physics.Closure.NSTriadKNResidualTransportOwnerFlowRound38Validation

echo "Round38 residual-transport-owner-flow checks passed"
