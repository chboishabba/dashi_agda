#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_operator_future_realization_round23.sh"
if [[ -f "$BASE_CHECKER" ]]; then
  bash "$BASE_CHECKER"
fi

FILES=(
  DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
  DASHI/Topology/TernaryPantsFrontierExact.agda
  DASHI/EverythingTernaryBranchGeometryRound24.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -vE '^[[:space:]]*--' "$f" \
      | grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!!\}|--allow-unsolved-metas|primTrustMe'; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

# One-step intrinsic ternary refinement / prefix geometry.
grep -q 'refinedSiblingsShareParentPrefix' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'child3Child6ShareParentPrefix' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'child3Child9ShareParentPrefix' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'child6Child9ShareParentPrefix' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda

# Exact Digit369 <-> canonical pants-slot correspondence.
grep -q 'digitSlotRoundTrip' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'slotDigitRoundTrip' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'canonicalPantsOutputsMatchTernarySlots' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'canonicalPantsHasThreeOutputs' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'canonicalCylinderPantsBridge' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'depthOneCylinderRefinementReturnsParent' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda

# Arbitrary-depth frontier equivalence and refinement/path compatibility.
grep -q 'addressPantsPathRoundTrip' DASHI/Topology/TernaryPantsFrontierExact.agda
grep -q 'pantsPathAddressRoundTrip' DASHI/Topology/TernaryPantsFrontierExact.agda
grep -q 'canonicalFrontierEquivalence' DASHI/Topology/TernaryPantsFrontierExact.agda
grep -q 'addressToPantsPathAppend' DASHI/Topology/TernaryPantsFrontierExact.agda
grep -q 'pantsPathToAddressAppend' DASHI/Topology/TernaryPantsFrontierExact.agda
grep -q 'depthThreeCylinderMapsToPants' DASHI/Topology/TernaryPantsFrontierExact.agda
grep -q 'allFiniteDepthsIndexedIsTrue' DASHI/Topology/TernaryPantsFrontierExact.agda
grep -q 'collisionFreeR3EmbeddingConstructedIsFalse' DASHI/Topology/TernaryPantsFrontierExact.agda

# Concrete 3D observation witness and fail-closed promotion boundary.
grep -q 'sampleChild3Voxel' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'sampleChild6Voxel' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'sampleChild9Voxel' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'voxelEmbeddingIsUltrametricIsometryIsFalse' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'padicFibreIsConnectedPantsSurfaceIsFalse' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda
grep -q 'smoothEmbeddedPantsThickeningConstructedIsFalse' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda

# Source metadata.
grep -q '10.1007/BF02698547' DASHI/Topology/TernaryCylinderPantsGeometryExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingTernaryBranchGeometryRound24.agda
else
  echo "agda unavailable: structural/fail-closed round-24 scan completed; no kernel-clean claim"
fi
