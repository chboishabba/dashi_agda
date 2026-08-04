#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/YangMills/PhysicalInvolutionParityExact.agda
  DASHI/Physics/YangMills/SetoidPhysicalInvolutionParityExact.agda
  DASHI/Physics/YangMills/BalabanCMP109CenteredParityExact.agda
  DASHI/Physics/YangMills/BalabanContourWordInverseExact.agda
  DASHI/Physics/YangMills/BalabanBishopFactorialPowerRecurrenceExact.agda
  DASHI/Physics/YangMills/BalabanBishopSeriesParityAndLimitExact.agda
  DASHI/Physics/YangMills/BalabanSU2AdjointParityExact.agda
  DASHI/Physics/YangMills/BalabanFederbushPairedContourCancellationExact.agda
  DASHI/Physics/YangMills/BalabanP06FiniteNeighbourGraphExact.agda
  DASHI/Physics/YangMills/BalabanP06PhysicalModelLeafExact.agda
  DASHI/Physics/YangMills/BalabanP11PhysicalPrefixTailEntropyExact.agda
  DASHI/Physics/YangMills/BalabanStepVFiniteGeometricBackendExact.agda
  DASHI/Physics/YangMills/BalabanP10P33PhysicalCutsetExact.agda
  DASHI/Physics/YangMills/BalabanGate4ParityIntegrationExact.agda
  DASHI/Physics/YangMills/YangMillsSIScalingEndpointExact.agda
  DASHI/Physics/YangMills/YangMillsRGParitySISpineExact.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound9SourceAudit.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound9Ledger.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound9Receipt.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound9Validation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSubmissionRound9Advance.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "round-nine tranche contains an explicit postulate or hole" >&2
  exit 1
fi

# Parity must be parameterized by a physical involution.
grep -q 'record PhysicalInvolutionFamily' \
  DASHI/Physics/YangMills/PhysicalInvolutionParityExact.agda
grep -q 'holonomyInverseContour' \
  DASHI/Physics/YangMills/BalabanContourWordInverseExact.agda
grep -q 'pairedWeightedContourLogsCancel' \
  DASHI/Physics/YangMills/BalabanFederbushPairedContourCancellationExact.agda

# Bishop recurrence work must use the real factorial and concrete power split.
grep -q 'oddFactorialSuccessor' \
  DASHI/Physics/YangMills/BalabanClayGate4BishopHalfRadiusRealEstimatesExact.agda
grep -q 'absPowOddSuccessorSplit' \
  DASHI/Physics/YangMills/BalabanBishopFactorialPowerRecurrenceExact.agda
grep -q 'bishopSinNeg' \
  DASHI/Physics/YangMills/BalabanBishopSeriesParityAndLimitExact.agda

# The concrete periodic graph route must not depend on the legacy count for its
# degree-eight theorem.
grep -q 'periodicConcreteBoundedDegreeEight' \
  DASHI/Physics/YangMills/BalabanP06FiniteNeighbourGraphExact.agda
grep -q 'legacyCountNeighboursCompatibilityLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP06FiniteNeighbourGraphExact.agda

# SI integration must keep inverse length distinct from mass and energy.
grep -q 'inverseLengthSilentlyIdentifiedWithSIMass = false' \
  DASHI/Physics/YangMills/YangMillsSIScalingEndpointExact.agda
grep -q 'mechanicalToSI' \
  DASHI/Physics/YangMills/YangMillsSIScalingEndpointExact.agda

roots=(
  DASHI/Physics/YangMills/PhysicalInvolutionParityExact.agda
  DASHI/Physics/YangMills/BalabanCMP109CenteredParityExact.agda
  DASHI/Physics/YangMills/BalabanContourWordInverseExact.agda
  DASHI/Physics/YangMills/BalabanBishopFactorialPowerRecurrenceExact.agda
  DASHI/Physics/YangMills/BalabanBishopSeriesParityAndLimitExact.agda
  DASHI/Physics/YangMills/BalabanSU2AdjointParityExact.agda
  DASHI/Physics/YangMills/BalabanFederbushPairedContourCancellationExact.agda
  DASHI/Physics/YangMills/BalabanP06FiniteNeighbourGraphExact.agda
  DASHI/Physics/YangMills/BalabanP06PhysicalModelLeafExact.agda
  DASHI/Physics/YangMills/BalabanP11PhysicalPrefixTailEntropyExact.agda
  DASHI/Physics/YangMills/BalabanStepVFiniteGeometricBackendExact.agda
  DASHI/Physics/YangMills/YangMillsSIScalingEndpointExact.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound9Validation.agda
  DASHI/Physics/PhysicsScalingLimitSpineValidation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSevenGroupAdvance.agda
)

for root_file in "${roots[@]}"; do
  scripts/run_agda29_parallel_check.sh "$root_file"
done
