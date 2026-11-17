#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

owners=(
  DASHI/Physics/YangMills/YangMillsLatticeStressWardSliceConservationExact.agda
  DASHI/Physics/Plasma/KSW668FullVectorMaxwellJetExact.agda
  DASHI/Physics/Motors/Circuit36927RecoveryEnergyBoundExact.agda
  DASHI/Physics/Motors/SmithFilsingerTimeIndexedTransferExact.agda
  DASHI/Physics/Motors/SmithFilsingerMidpointPhaseWorkExact.agda
  DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda
  DASHI/Physics/Motors/SmithFilsingerReplenishedCycleCapExact.agda
  DASHI/Promotion/MaxwellExteriorCalculusAdapter.agda
  DASHI/Physics/Motors/SmithFilsingerSpatialPortChainExact.agda
  DASHI/Physics/Motors/SmithFilsingerYeeCFLConeGuardExact.agda
  DASHI/Physics/Motors/SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerFiniteVolumeFaceIncidenceExact.agda
  DASHI/Physics/Motors/SmithFilsingerFullVectorIndexedFaceSampleExact.agda
  DASHI/Physics/Motors/SmithFilsingerSignedIndexedFaceFluxExact.agda
  DASHI/Physics/Motors/SmithFilsingerIndexedFaceSourceWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerIndexedFaceIncidenceExact.agda
  DASHI/Physics/Motors/SmithFilsingerIndexedSignedCellStokesExact.agda
  DASHI/Physics/Motors/SmithFilsingerTimedSpatialPortChainExact.agda
  DASHI/Physics/Motors/SmithFilsingerSpatialSourceBoundaryWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerSourceMaxwellBoundaryWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerCloudCausalWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerMaxwellMaterialEnergyCutExact.agda
  DASHI/Physics/Motors/SmithFilsingerDispersiveMaterialPortExact.agda
  DASHI/Physics/Motors/SmithFilsingerDispersiveMaterialWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerFullVectorPoyntingPortWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerSpatialSourceCapWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerMaxwellTimedSpatialWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerOpenBoundaryPoyntingGaussExact.agda
  DASHI/Physics/Motors/SmithFilsingerSpaceTimePoyntingTelescopeExact.agda
)
new_owners=(
  DASHI/Physics/Motors/SmithFilsingerSpatialPortChainExact.agda
  DASHI/Physics/Motors/SmithFilsingerYeeCFLConeGuardExact.agda
  DASHI/Physics/Motors/SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerFiniteVolumeFaceIncidenceExact.agda
  DASHI/Physics/Motors/SmithFilsingerFullVectorIndexedFaceSampleExact.agda
  DASHI/Physics/Motors/SmithFilsingerSignedIndexedFaceFluxExact.agda
  DASHI/Physics/Motors/SmithFilsingerIndexedFaceSourceWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerIndexedFaceIncidenceExact.agda
  DASHI/Physics/Motors/SmithFilsingerIndexedSignedCellStokesExact.agda
  DASHI/Physics/Motors/SmithFilsingerTimedSpatialPortChainExact.agda
  DASHI/Physics/Motors/SmithFilsingerSpatialSourceBoundaryWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerSourceMaxwellBoundaryWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerCloudCausalWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerMaxwellMaterialEnergyCutExact.agda
  DASHI/Physics/Motors/SmithFilsingerDispersiveMaterialWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerFullVectorPoyntingPortWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerSpatialSourceCapWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerMaxwellTimedSpatialWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerOpenBoundaryPoyntingGaussExact.agda
  DASHI/Physics/Motors/SmithFilsingerSpaceTimePoyntingTelescopeExact.agda
)
for f in "${owners[@]}"; do test -s "$f"; done
# Do not use a regex for Agda's literal {!!} hole. The old
# double-escaped ERE failed to match it and could silently admit a hole.
# grep -F tests the exact concrete token; the optional source guard rejects
# explicit postulates and compiler-escape pragmas in all new owners.
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)' "${new_owners[@]}" \
   || grep -nF '{!!}' "${new_owners[@]}" \
   || grep -nE '^[[:space:]]*\{-# *(TERMINATING|NON_TERMINATING|OPTIONS[^}]*--(allow-unsolved-metas|type-in-type|no-termination-check|no-positivity-check|no-coverage-check))' "${new_owners[@]}"; then
  echo "REJECT: postulate, explicit proof hole, or unsafe Agda pragma" >&2
  exit 1
fi

# No Python surrogate or simulation: require actual pinned Agda type-check.
scripts/run_agda29_parallel_check.sh "${new_owners[@]}"
echo "PASS pinned Agda 2.9 on all designated Maxwell/material/cloud/timed-spatial formal welds"
