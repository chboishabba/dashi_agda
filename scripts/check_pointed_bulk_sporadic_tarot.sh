#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ "${POINTED_BULK_SKIP_BASE:-0}" != "1" ]]; then
  bash scripts/check_conscious_access_round5.sh
  CABARLAH_SKIP_ROUND5=1 bash scripts/check_cabarlah_palestine_formalism.sh
fi

FILES=(
  DASHI/Biology/PointedTernaryBulkExact.agda
  DASHI/Biology/DecimalTenTernaryPresentationExact.agda
  DASHI/Biology/ThreeSixNineMoonshineScaleExact.agda
  DASHI/Biology/ReducedFiftyThreeOrbitCandidateExact.agda
  DASHI/Biology/SporadicTarotDependencyExact.agda
  DASHI/Biology/PointedBulkReducedMoonshineBoundary.agda
  DASHI/Biology/PointedBulkSporadicTarotSourceAtlas.agda
  DASHI/Biology/PointedBulkSporadicTarotEverything.agda
  DASHI/Governance/CabarlahTraumaProjectionBridgeExact.agda
  DASHI/Governance/Everything.agda
  DASHI/PointedBulkSporadicTarotCabarlahBoundary.agda
  DASHI/PointedBulkSporadicTarotCabarlahRegression.agda
  DASHI/EverythingPointedBulkSporadicTarot.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required pointed-bulk/sporadic-Tarot source is missing: $file" >&2
    exit 1
  fi

  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

# Exact arithmetic and action guards.
grep -q 'pointedBulkDimensionIs196830' \
  DASHI/Biology/PointedTernaryBulkExact.agda
grep -q 'pointedBulkEqualsUnpointedPlusPointed' \
  DASHI/Biology/PointedTernaryBulkExact.agda
grep -q 'rotatePointedFourReturns' \
  DASHI/Biology/PointedTernaryBulkExact.agda
grep -q 'pointedA2MultiplicityIsZero' \
  DASHI/Biology/PointedTernaryBulkExact.agda
grep -q 'decimalAndPointedBulkDimensionsAgree' \
  DASHI/Biology/DecimalTenTernaryPresentationExact.agda
grep -q 'tenSectorListIsRawD4IsotypicDecompositionIsFalse' \
  DASHI/Biology/DecimalTenTernaryPresentationExact.agda
grep -q 'fiftyFourIsTwoTimesThreeCubed' \
  DASHI/Biology/ThreeSixNineMoonshineScaleExact.agda
grep -q 'tenIrrepOrientationMatchesSectorCount' \
  DASHI/Biology/ThreeSixNineMoonshineScaleExact.agda
grep -q 'arithmeticEqualityTransfersGroupActionIsFalse' \
  DASHI/Biology/ThreeSixNineMoonshineScaleExact.agda

# Reduced-53 promotion guards.
grep -q 'candidateR53DimensionIsFiftyThree' \
  DASHI/Biology/ReducedFiftyThreeOrbitCandidateExact.agda
grep -q 'candidateInvolutionIsInvolutive' \
  DASHI/Biology/ReducedFiftyThreeOrbitCandidateExact.agda
grep -q 'oneFixedPointCandidateLabelsSporadicGroupsIsFalse' \
  DASHI/Biology/ReducedFiftyThreeOrbitCandidateExact.agda
grep -q 'signTwistOccursSevenPromotionsAfterArithmetic' \
  DASHI/Biology/PointedBulkReducedMoonshineBoundary.agda
grep -q 'S26ActionMayBeReusedWithoutConstructionIsFalse' \
  DASHI/Biology/PointedBulkReducedMoonshineBoundary.agda

# Sporadic inventory, Tarot, and political-authority guards.
grep -q 'sporadicInventoryCountIsTwentySix' \
  DASHI/Biology/SporadicTarotDependencyExact.agda
grep -q 'co4HasNoConwaySporadicReferent' \
  DASHI/Biology/SporadicTarotDependencyExact.agda
grep -q 'inventoryMinusArcanaCountIsFour' \
  DASHI/Biology/SporadicTarotDependencyExact.agda
grep -q 'typedDependencyGraphRetainsEdgeAuthorityIsTrue' \
  DASHI/Biology/SporadicTarotDependencyExact.agda
grep -q 'reflectingPoolReadingDoesNotInferMotive' \
  DASHI/Governance/CabarlahTraumaProjectionBridgeExact.agda
grep -q 'pineGapConcernDoesNotVerifySpecificStrike' \
  DASHI/Governance/CabarlahTraumaProjectionBridgeExact.agda

echo "Pointed bulk / sporadic Tarot static guards passed."

scripts/run_agda29_parallel_check.sh \
  DASHI/PointedBulkSporadicTarotCabarlahRegression.agda \
  DASHI/PointedBulkSporadicTarotCabarlahBoundary.agda \
  DASHI/EverythingPointedBulkSporadicTarot.agda
