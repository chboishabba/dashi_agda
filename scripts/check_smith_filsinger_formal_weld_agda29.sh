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
)
for f in "${owners[@]}"; do
  test -s "$f"
done
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\\{!!\\}'     DASHI/Physics/Motors/SmithFilsingerSourceMaxwellBoundaryWeldExact.agda     DASHI/Physics/Motors/SmithFilsingerCloudCausalWeldExact.agda; then
  echo "REJECT: explicit postulate or hole in formal weld" >&2
  exit 1
fi
# The verified dependency walker is the repo-owned Agda 2.9 pinned wrapper.
# Do NOT infer a kernel PASS when Nix/Agda is missing.
scripts/run_agda29_parallel_check.sh  DASHI/Physics/Motors/SmithFilsingerSourceMaxwellBoundaryWeldExact.agda  DASHI/Physics/Motors/SmithFilsingerCloudCausalWeldExact.agda
echo "PASS: pinned Agda 2.9 checked both F10/F13/F14/F15/F16 weld consumers"
