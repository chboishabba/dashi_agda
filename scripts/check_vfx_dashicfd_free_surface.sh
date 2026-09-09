#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

TARGET="DASHI/Physics/VFX/DashiCFDFreeSurfaceWeldExact.agda"

grep -q 'shallowWaterReceiptIsNotFullThreeDimensionalFreeSurfaceNS' "$TARGET"
grep -q 'finiteStableRunDoesNotProvePhysicalCalibration' "$TARGET"
grep -q 'hydrostaticHullLoadProxyIsNotStructuralFEA' "$TARGET"
grep -q 'domainMassChangeIsNotClosedDomainConservationProof' "$TARGET"
grep -q 'dashicfdRunDoesNotProveNavierStokesClay' "$TARGET"
grep -q 'shotGeometryEqualsSolverGeometry' "$TARGET"
grep -q 'receiptDigestBindsAllNumericalArtifacts' "$TARGET"

if command -v agda >/dev/null 2>&1; then
  AGDA_STDLIB="${AGDA_STDLIB:-/usr/share/agda-stdlib}"
  agda -i . -i "$AGDA_STDLIB" "$TARGET"
fi

echo "dashiCFD free-surface VFX weld gate: source boundary checks passed"
