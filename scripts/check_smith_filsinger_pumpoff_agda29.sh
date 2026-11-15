#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
files=(
  DASHI/Physics/Motors/Circuit36927ComponentGraphExact.agda
  DASHI/Physics/Motors/Circuit36927SwitchStateExact.agda
  DASHI/Physics/Motors/Circuit36927RecoveryEnergyBoundExact.agda
  DASHI/Promotion/MaxwellExteriorCalculusAdapter.agda
  DASHI/Physics/Motors/SmithFilsingerTimeIndexedTransferExact.agda
  DASHI/Physics/Motors/SmithFilsingerHybridRegimeStudyBidiExact.agda
  DASHI/Physics/Motors/SmithFilsingerPumpOffDualPathExact.agda
)
for f in "${files[@]}";do test -s "$f";done
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)' "${files[@]}";then
  echo "Unjustified postulate detected" >&2; exit 1
fi
for f in "${files[@]}";do
  scripts/run_agda29_parallel_check.sh "$f"
done
echo "PASS Agda 2.9 kernel accepted seven same-source motors/Maxwell modules"
