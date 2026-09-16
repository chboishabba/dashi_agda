#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Education/DigitalESDPaperTypeRequirementParetoExact.agda
REGRESSION=DASHI/Education/DigitalESDPaperTypeRequirementRegression.agda

for file in "$OWNER" "$REGRESSION"; do
  [[ -f "$file" ]] || { echo "required paper-type source is missing: $file" >&2; exit 1; }
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '10.1111/j.1365-2648.2005.03621.x' "$OWNER"
grep -q '10.1186/s41073-019-0064-8' "$OWNER"
grep -q '10.1136/bmj.n71' "$OWNER"
grep -q '^currentPaperType :' "$OWNER"
grep -q '^digitalESDPaperRequirementSystem :' "$OWNER"
grep -q '^currentConceptualReviewFrontier :' "$OWNER"
grep -q '^systematicReviewLabelRequiresProtocol :' "$OWNER"
grep -q '^conceptualReviewDoesNotRequireSameObjectInterventionLCA :' "$OWNER"
grep -q '^methodCitationDoesNotCloseExecution :' "$OWNER"
grep -q '^prismaDoesNotAutomaticallyApplyToConceptualReview :' "$OWNER"

grep -q '^currentPaperTypeRegression :' "$REGRESSION"
grep -q '^conceptualSearchRequiredRegression :' "$REGRESSION"
grep -q '^conceptualSameObjectLCANotRequiredRegression :' "$REGRESSION"
grep -q '^systematicProtocolRequiredRegression :' "$REGRESSION"
grep -q '^empiricalSameObjectLCARequiredRegression :' "$REGRESSION"
grep -q '^currentMissingSearchReceiptRegression :' "$REGRESSION"

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh "$REGRESSION"
elif command -v agda >/dev/null 2>&1; then
  agda -i . "$REGRESSION"
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "paper-type source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi
