#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Education/DigitalESDStructuredSearchExact.agda
REGRESSION=DASHI/Education/DigitalESDStructuredSearchRegression.agda

for file in "$OWNER" "$REGRESSION"; do
  [[ -f "$file" ]] || { echo "required structured-search source is missing: $file" >&2; exit 1; }
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '10.1186/s13643-020-01542-z' "$OWNER"
grep -q '10.1016/j.jclinepi.2016.01.021' "$OWNER"
grep -q '^canonicalSearchQueryFamilies :' "$OWNER"
grep -q '^canonicalObservedOpenWebSearches :' "$OWNER"
grep -q '^canonicalStructuredSearchLedger :' "$OWNER"
grep -q '^openWebSnowballDoesNotCloseTransparentStructuredSearch :' "$OWNER"
grep -q '^searchMethodCitationDoesNotPromoteSystematicReview :' "$OWNER"
grep -q '^plannedDatabaseDoesNotCreateExecutionReceipt :' "$OWNER"
grep -q '^searchHitDoesNotCreateIncludedStudy :' "$OWNER"
grep -q '^searchResultSnippetDoesNotPayFullSourceClaim :' "$OWNER"

grep -q '^queryFamilyRegression :' "$REGRESSION"
grep -q '^openWebExecutionRegression :' "$REGRESSION"
grep -q '^scopusExecutionRegression :' "$REGRESSION"
grep -q '^wosExecutionRegression :' "$REGRESSION"
grep -q '^ericExecutionRegression :' "$REGRESSION"
grep -q '^acmExecutionRegression :' "$REGRESSION"
grep -q '^ieeeExecutionRegression :' "$REGRESSION"
grep -q '^structuredSearchStillOpenRegression :' "$REGRESSION"

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh "$REGRESSION"
elif command -v agda >/dev/null 2>&1; then
  agda -i . "$REGRESSION"
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "structured-search source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi
