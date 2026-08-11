#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

bash scripts/check_ns_residual_transport_owner_flow_round38.sh

files=(
  DASHI/Physics/Closure/NSTriadKNPeriodicKernelNearSmoothSplitRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHGoodResidualShellTransportRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHGoodSquaredBudgetRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNPeriodicPVHHGoodNearSmoothOwnerRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadRestrictedGainDensityRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNComCrossChannelRoundTripRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNF4PairNormalizationRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNF4ProjectedOutputPairingRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNF4GlobalOutputFiberPartitionRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNNineOwnerDualNoGoRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHGoodBadThresholdOptimizationRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNCancellationOrderRound39Exact.agda
  DASHI/Physics/Closure/NSTriadKNPeriodicPVOddComF4Round39Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
  if grep -En '(^|[[:space:]])(postulate|primitive)[[:space:]]|\{!!\}|\?|trustMe|unsafe|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|funext|Properties\.WithK|unique⇒irrelevant|--with-K' "$file"; then
    echo "forbidden proof escape in $file" >&2
    exit 1
  fi
done

# HH-good: split torus algebra, preserve residual, budget the threshold, and
# keep the smooth periodic correction out of the viscosity tax.
grep -q 'periodicKernelTransformSplits' DASHI/Physics/Closure/NSTriadKNPeriodicKernelNearSmoothSplitRound39Exact.agda
grep -q 'periodicWeightedIncrementSplits' DASHI/Physics/Closure/NSTriadKNPeriodicKernelNearSmoothSplitRound39Exact.agda
grep -q 'lineResidualCommutesWithFiniteWeightedShellSum' DASHI/Physics/Closure/NSTriadKNHHGoodResidualShellTransportRound39Exact.agda
grep -q 'weightedResidualIgnoresParallelPerturbation' DASHI/Physics/Closure/NSTriadKNHHGoodResidualShellTransportRound39Exact.agda
grep -q 'squaredHHGoodBudgetAbsorption' DASHI/Physics/Closure/NSTriadKNHHGoodSquaredBudgetRound39Exact.agda
grep -q 'nearSmoothHHGoodAggregateBound' DASHI/Physics/Closure/NSTriadKNPeriodicPVHHGoodNearSmoothOwnerRound39Exact.agda
grep -q 'hhGoodOwnerEstimateFromNearSmooth' DASHI/Physics/Closure/NSTriadKNPeriodicPVHHGoodNearSmoothOwnerRound39Exact.agda

# HH-bad: same-sample gain density; no differentiated Bool mask.
grep -q 'maskedGainGoodSampleZero' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedGainDensityRound39Exact.agda
grep -q 'finiteRestrictedGainDensityBound' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedGainDensityRound39Exact.agda
grep -q 'restrictedGainBelowInverseShellCharge' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedGainDensityRound39Exact.agda

# Com: nilpotent cross channels and only diagonal round trips survive squared
grep -q 'upperCrossChannelNilpotent' DASHI/Physics/Closure/NSTriadKNComCrossChannelRoundTripRound39Exact.agda
grep -q 'lowerCrossChannelNilpotent' DASHI/Physics/Closure/NSTriadKNComCrossChannelRoundTripRound39Exact.agda
grep -q 'oddSquareIsCrossFibreRoundTrips' DASHI/Physics/Closure/NSTriadKNComCrossChannelRoundTripRound39Exact.agda
grep -q 'involutionSwapsUpperToLower' DASHI/Physics/Closure/NSTriadKNComCrossChannelRoundTripRound39Exact.agda
grep -q 'jEquivarianceForcesCrossChannelEquality' DASHI/Physics/Closure/NSTriadKNComCrossChannelRoundTripRound39Exact.agda

# F4: correct the no-half convention, identify actual projected output pairing,
# partition the full enumeration by literal cutoff outputs, and close finite
# Galerkin convection energy cancellation.
grep -q 'swapFixedStoredPairIsDoubleOrdered' DASHI/Physics/Closure/NSTriadKNF4PairNormalizationRound39Exact.agda
grep -q 'normalizedPairFoldEqualsOrderedFold' DASHI/Physics/Closure/NSTriadKNF4PairNormalizationRound39Exact.agda
grep -q 'projectedOutputEnergyPairingEqualsOrderedFiberFold' DASHI/Physics/Closure/NSTriadKNF4ProjectedOutputPairingRound39Exact.agda
grep -q 'literalOutputPartitionPermutation' DASHI/Physics/Closure/NSTriadKNF4GlobalOutputFiberPartitionRound39Exact.agda
grep -q 'literalConvectionPairingEqualsOrderedIncidenceFold' DASHI/Physics/Closure/NSTriadKNF4GlobalOutputFiberPartitionRound39Exact.agda
grep -q 'literalProjectedGalerkinConvectionEnergyZero' DASHI/Physics/Closure/NSTriadKNF4GlobalOutputFiberPartitionRound39Exact.agda
grep -q 'literalConvectionPairingEqualsOrderedIncidenceFoldConstructed = true' DASHI/Physics/Closure/NSTriadKNF4GlobalOutputFiberPartitionRound39Exact.agda

# Reserve/no-go and late-tax ordering.
grep -q 'dualCertificateForcesEtaTotalAtLeastOne' DASHI/Physics/Closure/NSTriadKNNineOwnerDualNoGoRound39Exact.agda
grep -q 'certifiedThresholdAtOrAboveOneIsArchitectureNoGo' DASHI/Physics/Closure/NSTriadKNHHGoodBadThresholdOptimizationRound39Exact.agda
grep -q 'preTaxPositiveCannotExceedRaw' DASHI/Physics/Closure/NSTriadKNCancellationOrderRound39Exact.agda
grep -q 'finalTaxCannotExceedRawPositive' DASHI/Physics/Closure/NSTriadKNCancellationOrderRound39Exact.agda

# Load-bearing provenance metadata.
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNPeriodicKernelNearSmoothSplitRound39Exact.agda
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNHHGoodResidualShellTransportRound39Exact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedGainDensityRound39Exact.agda
grep -q '10.1002/cpa.3160410704' DASHI/Physics/Closure/NSTriadKNComCrossChannelRoundTripRound39Exact.agda
grep -q '10.1007/BF02547354' DASHI/Physics/Closure/NSTriadKNF4GlobalOutputFiberPartitionRound39Exact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNF4GlobalOutputFiberPartitionRound39Exact.agda

# Keep the genuinely physical analytic producers fail-closed.  F4 is the one
# frontier seam intentionally flipped true in Round 39.
grep -q 'literalTorusStrainNearSmoothSplitConstructed = false' DASHI/Physics/Closure/NSTriadKNPeriodicKernelNearSmoothSplitRound39Exact.agda
grep -q 'smoothPeriodicCorrectionOwnerBoundConstructed = false' DASHI/Physics/Closure/NSTriadKNPeriodicKernelNearSmoothSplitRound39Exact.agda
grep -q 'physicalPVResidualPreservingShellDecompositionConstructed = false' DASHI/Physics/Closure/NSTriadKNHHGoodResidualShellTransportRound39Exact.agda
grep -q 'physicalUnsquaredPVHHGoodOwnerAbsorptionConstructed = false' DASHI/Physics/Closure/NSTriadKNHHGoodSquaredBudgetRound39Exact.agda
grep -q 'physicalPeriodicPVHHGoodNearSmoothEstimateConstructed = false' DASHI/Physics/Closure/NSTriadKNPeriodicPVHHGoodNearSmoothOwnerRound39Exact.agda
grep -q 'physicalHHBadGainDensityCellsConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedGainDensityRound39Exact.agda
grep -q 'physicalLuoCriticalDissipationSmallnessConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadRestrictedGainDensityRound39Exact.agda
grep -q 'physicalComRoundTripGramRealizationConstructed = false' DASHI/Physics/Closure/NSTriadKNComCrossChannelRoundTripRound39Exact.agda
grep -q 'physicalComJEquivarianceConstructed = false' DASHI/Physics/Closure/NSTriadKNComCrossChannelRoundTripRound39Exact.agda
grep -q 'literalConvectionPairingNormalizationIdentified = false' DASHI/Physics/Closure/NSTriadKNF4PairNormalizationRound39Exact.agda
grep -q 'physicalNineOwnerDualNoGoCertificateConstructed = false' DASHI/Physics/Closure/NSTriadKNNineOwnerDualNoGoRound39Exact.agda
grep -q 'physicalThresholdTaxProfileConstructed = false' DASHI/Physics/Closure/NSTriadKNHHGoodBadThresholdOptimizationRound39Exact.agda
grep -q 'physicalCancellationHierarchyIdentified = false' DASHI/Physics/Closure/NSTriadKNCancellationOrderRound39Exact.agda

chmod +x scripts/agda29_without_k_wrapper.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI.Physics.Closure.NSTriadKNPeriodicPVOddComF4Round39Validation

echo "Round39 periodic-PV/odd-Com/F4 checks passed"
