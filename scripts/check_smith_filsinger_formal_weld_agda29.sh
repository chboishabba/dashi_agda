#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

owners=(
  DASHI/Physics/Motors/Circuit36927RecoveryEnergyBoundExact.agda
  DASHI/Physics/Motors/SmithFilsingerTimeIndexedTransferExact.agda
  DASHI/Physics/Motors/SmithFilsingerMidpointPhaseWorkExact.agda
  DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda
  DASHI/Physics/Motors/SmithFilsingerReplenishedCycleCapExact.agda
  DASHI/Promotion/MaxwellExteriorCalculusAdapter.agda
  DASHI/Physics/Motors/SmithFilsingerSourceMaxwellBoundaryWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerCloudCausalWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerMaxwellMaterialEnergyCutExact.agda
)
new_owners=(
  DASHI/Physics/Motors/SmithFilsingerSourceMaxwellBoundaryWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerCloudCausalWeldExact.agda
  DASHI/Physics/Motors/SmithFilsingerMaxwellMaterialEnergyCutExact.agda
)
for f in "${owners[@]}"; do test -s "$f"; done
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\\{!!\\}' "${new_owners[@]}"; then
  echo "REJECT: explicit postulate or proof hole" >&2
  exit 1
fi
# No Python surrogate or simulation: require actual pinned Agda type-check.
scripts/run_agda29_parallel_check.sh "${new_owners[@]}"
echo "PASS pinned Agda 2.9 source-Maxwell, causal cloud and material-cut formal welds"
