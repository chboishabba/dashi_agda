#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python3 scripts/check_ns_localized_bkm_route.py

AGDA_BIN="${AGDA_BIN:-agda}"
AGDA_ARGS_STRING="${AGDA_ARGS:--i . -i DCHoTT-Agda -i vendor/bishop -i cubical -l standard-library}"
read -r -a AGDA_ARGS_ARRAY <<<"$AGDA_ARGS_STRING"

TARGETS=(
  DASHI/Physics/Closure/NSTriadKNPeriodicLittlewoodPaleyBonyExact.agda
  DASHI/Physics/Closure/NSTriadKNProfileDepthGeometryCutoffIndexedExact.agda
  DASHI/Physics/Closure/NSTriadKNResidueScaleOperatorGapExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoExplicitCutoffLocalizedCriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNLocalizedBKMSourceAndTargetAudit.agda
  DASHI/Physics/Closure/NSTriadKNLittlewoodPaleyInfrastructureInventory.agda
  DASHI/Physics/Closure/NSTriadKNBlockerToLocalizedBKMCompatibility.agda
  DASHI/Physics/Closure/NSTriadKNAnalyticBlockerAuthorityAudit.agda
  DASHI/Physics/Closure/NSTriadKNLocalizedBKMRouteIntegration.agda
)

for target in "${TARGETS[@]}"; do
  echo "Checking: $target"
  "$AGDA_BIN" "${AGDA_ARGS_ARRAY[@]}" "$target"
done

echo "PASS: focused exact localized-BKM Agda tranche"
