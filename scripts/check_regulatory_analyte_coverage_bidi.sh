#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
  DASHI/Chemistry/Everything.agda
  DASHI/RegulatoryAnalyteCoverageValidation.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required regulatory-analyte source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^complianceCannotRecoverCompleteOffPanelState :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
grep -q '^certificateCannotRecoverCompleteOffPanelState :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
grep -q '^offPanelCannotAutoPromoteToUndetectable :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
grep -q '^socialMediaAssertionCannotAutoPromoteToVerifiedBypass :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda
grep -q '^canonicalRegulatoryAnalyteCoverageBoundary :' DASHI/Chemistry/RegulatoryAnalyteCoverageBidiExact.agda

scripts/run_agda29_parallel_check.sh DASHI/RegulatoryAnalyteCoverageValidation.agda
