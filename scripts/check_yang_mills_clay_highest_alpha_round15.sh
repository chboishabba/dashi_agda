#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanClayLowerBoundCountermodelExact.agda
  DASHI/Physics/YangMills/BalabanClayTransferGapDefectTelescopingExact.agda
  DASHI/Physics/YangMills/BalabanClayPhysicalScaleExponentExact.agda
  DASHI/Physics/YangMills/BalabanClayUniformPerronContractionExact.agda
  DASHI/Physics/YangMills/BalabanClayNormingFamilyOperatorBoundExact.agda
  DASHI/Physics/YangMills/BalabanClayTransferHamiltonianGapSeparationExact.agda
  DASHI/Physics/YangMills/BalabanClayExactOSPullbackRecombinationExact.agda
  DASHI/Physics/YangMills/BalabanClayDenseCoreSpectralGapExact.agda
  DASHI/Physics/YangMills/BalabanClayLocalNoncollapseExact.agda
  DASHI/Physics/YangMills/BalabanClayObservableGapEdgeExact.agda
  DASHI/Physics/YangMills/BalabanClaySpectralUVCompatibilityExact.agda
  DASHI/Physics/YangMills/BalabanClayMassGapGatePackageExact.agda
  DASHI/Physics/YangMills/BalabanClayMirShabirScopeAuditExact.agda
  DASHI/Physics/YangMills/BalabanClayExternalAttemptStressTestsExact.agda
  DASHI/Physics/YangMills/BalabanP33InverseDexpReducedOperatorExact.agda
  DASHI/Physics/YangMills/BalabanP33GroupProductDistanceTelescopingExact.agda
  DASHI/Physics/YangMills/BalabanP33SecondChartRadiusCalibrationExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound15Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas' "${files[@]}"; then
  echo "Clay highest-alpha round fifteen contains a postulate, hole, unsafe escape, or unsolved-meta option" >&2
  exit 1
fi

checks=(
  'BalabanClayLowerBoundCountermodelExact.agda:factorMismatchCountermodel'
  'BalabanClayTransferGapDefectTelescopingExact.agda:finiteDefectChainTelescopes'
  'BalabanClayTransferGapDefectTelescopingExact.agda:summabilityWithoutStrictBudgetCounterexample'
  'BalabanClayPhysicalScaleExponentExact.agda:physicalMassScaleBridge'
  'BalabanClayPhysicalScaleExponentExact.agda:latticeEnvelopeImpliesPhysicalEnvelope'
  'BalabanClayUniformPerronContractionExact.agda:noUniformDiameterBound'
  'BalabanClayNormingFamilyOperatorBoundExact.agda:oneObservableDoesNotControlOperatorNorm'
  'BalabanClayTransferHamiltonianGapSeparationExact.agda:positiveTransferGapRequiresExplicitPhysicalConversion'
  'BalabanClayExactOSPullbackRecombinationExact.agda:exactPullbackPreservesReflectionPositivity'
  'BalabanClayDenseCoreSpectralGapExact.agda:denseLocalClusteringImpliesGap'
  'BalabanClayLocalNoncollapseExact.agda:localPositiveOSNormForcesNonzeroVector'
  'BalabanClayObservableGapEdgeExact.agda:observableGapEdgeDetection'
  'BalabanClaySpectralUVCompatibilityExact.agda:assembleSpectralUVCompatibility'
  'BalabanClayMassGapGatePackageExact.agda:assembleMandatoryClayMassGapGates'
  'BalabanClayMirShabirScopeAuditExact.agda:part2ContainsScalingTransportInPublishedComponent'
  'BalabanClayExternalAttemptStressTestsExact.agda:finiteConeDiameterDoesNotGiveUniformDiameter'
  'BalabanP33InverseDexpReducedOperatorExact.agda:inverseDexpActsAsTwoSidedInverse'
  'BalabanP33GroupProductDistanceTelescopingExact.agda:productDistanceTelescoping'
  'BalabanP33SecondChartRadiusCalibrationExact.agda:secondChartEnvelopeFitsDiagonalAllocationExactly'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Source ownership must travel with every imported theorem boundary.
grep -q '10.4007/annals.2010.171.1707' \
  DASHI/Physics/YangMills/BalabanClayUniformPerronContractionExact.agda
grep -q '10.1142/S0219887826501136' \
  DASHI/Physics/YangMills/BalabanClayTransferGapDefectTelescopingExact.agda
grep -q '10.1007/BF01645738' \
  DASHI/Physics/YangMills/BalabanClayExactOSPullbackRecombinationExact.agda
grep -q '10.1103/PhysRevLett.30.1343' \
  DASHI/Physics/YangMills/BalabanClaySpectralUVCompatibilityExact.agda
grep -q '10.1002/prop.70097' \
  DASHI/Physics/YangMills/BalabanClayMirShabirScopeAuditExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33InverseDexpReducedOperatorExact.agda
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33GroupProductDistanceTelescopingExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound15Validation.agda
