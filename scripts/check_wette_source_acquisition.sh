#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/SourceAcquisitionGeometryExact.agda
  DASHI/Foundations/WettePrimaryTextAcquisitionPlanExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "missing source-acquisition file: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'bibliographicMetadataEqualsFullTextAccessIsFalse' \
  DASHI/Core/SourceAcquisitionGeometryExact.agda
grep -q 'accessRouteEqualsPrimaryTextInspectionIsFalse' \
  DASHI/Core/SourceAcquisitionGeometryExact.agda
grep -q 'interlibraryLoanIsLegitimatePrimaryAcquisitionRouteIsTrue' \
  DASHI/Core/SourceAcquisitionGeometryExact.agda
grep -q 'Journal of Symbolic Logic 39' \
  DASHI/Foundations/WettePrimaryTextAcquisitionPlanExact.agda
grep -q 'Journal of Symbolic Logic 41' \
  DASHI/Foundations/WettePrimaryTextAcquisitionPlanExact.agda
grep -q 'International Logic Review 9' \
  DASHI/Foundations/WettePrimaryTextAcquisitionPlanExact.agda
grep -q 'acquisitionRouteAloneUpgradesHistoricalSemanticsIsFalse' \
  DASHI/Foundations/WettePrimaryTextAcquisitionPlanExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/SourceAcquisitionGeometryExact.agda \
  DASHI/Foundations/WettePrimaryTextAcquisitionPlanExact.agda
