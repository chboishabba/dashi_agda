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
  DASHI/Biology/TarotCarrierExact.agda
  DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
  DASHI/Biology/JMDSporadicTarotV2Regression.agda
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

grep -q 'pointedBulkDimensionIs196830' DASHI/Biology/PointedTernaryBulkExact.agda
grep -q 'candidateR53DimensionIsFiftyThree' DASHI/Biology/ReducedFiftyThreeOrbitCandidateExact.agda
grep -q 'sporadicInventoryCountIsTwentySix' DASHI/Biology/SporadicTarotDependencyExact.agda
grep -q 'majorArcanaCountIsTwentyTwo' DASHI/Biology/TarotCarrierExact.agda

# JMD poster transcription and non-promotion guards.
grep -q 'jmdV2Assignment Sporadic.M11' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'jmdV2Assignment Sporadic.Fi22' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'co4StrengthAssignment' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'actualInventoryAccounting' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'posterCardCountIsTwentyTwo' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'posterSuppliesTotalS26ToA22MapIsFalse' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'omittedGroupsMayBeAssignedWithoutRationaleIsFalse' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda

echo "Pointed bulk / sporadic Tarot / JMD v2 static guards passed."

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/JMDSporadicTarotV2Regression.agda \
  DASHI/PointedBulkSporadicTarotCabarlahRegression.agda \
  DASHI/PointedBulkSporadicTarotCabarlahBoundary.agda \
  DASHI/EverythingPointedBulkSporadicTarot.agda
