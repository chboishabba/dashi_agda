#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PRINCIPLES=DASHI/Education/DigitalESDTransferablePedagogicalPrinciplesExact.agda
PRINCIPLES_REG=DASHI/Education/DigitalESDTransferablePedagogicalPrinciplesRegression.agda
MATRIX=DASHI/Education/DigitalESDTransformativePrincipleMatrixExact.agda
MATRIX_REG=DASHI/Education/DigitalESDTransformativePrincipleMatrixRegression.agda
DOC=docs/digital-esd-transformative-principles.md

for file in "$PRINCIPLES" "$PRINCIPLES_REG" "$MATRIX" "$MATRIX_REG" "$DOC"; do
  [[ -f "$file" ]] || { echo "required digital-ESD principle source is missing: $file" >&2; exit 1; }
done

for file in "$PRINCIPLES" "$PRINCIPLES_REG" "$MATRIX" "$MATRIX_REG"; do
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^transferablePrincipleCount : Nat' "$PRINCIPLES"
grep -q '^situatedRelationalEngagementRow :' "$PRINCIPLES"
grep -q '^feedbackAsRevisableSignalRow :' "$PRINCIPLES"
grep -q '^constitutiveLearnerAgencyRow :' "$PRINCIPLES"
grep -q '^adaptiveSupportWithLocalChoiceRow :' "$PRINCIPLES"
grep -q '^pluralSituatedObserversRow :' "$PRINCIPLES"
grep -q '^contextualCustodianshipRow :' "$PRINCIPLES"
grep -q '^iterativeEvidenceReturnAndRechartingRow :' "$PRINCIPLES"
grep -q '^coarseProxyDoesNotDetermineContextAdequateIntervention :' "$PRINCIPLES"
grep -q '^canonicalTransferablePrinciplesBoundary :' "$PRINCIPLES"

grep -q '^matrixRowCountRegression :' "$MATRIX_REG"
grep -q '^scalingConditionsRetainedRegression :' "$MATRIX_REG"
grep -q 'professionalDevelopmentCondition' "$MATRIX"
grep -q '^contextualCustodianshipConstraintRow :' "$MATRIX"
grep -q '^sustainabilityEvidenceDoesNotBecomeAliceSourceFinding :' "$MATRIX"
grep -q '^principleConstraintPairDoesNotCreateEmpiricalDigitalESDEffect :' "$MATRIX"
grep -q '^canonicalTransformativePrincipleMatrixBoundary :' "$MATRIX"

grep -q '^# Source-attributed transformative principles for digital ESD$' "$DOC"
grep -q 'professional development' "$DOC"
grep -q 'Who participates? Who interprets? Who benefits?' "$DOC"

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh "$PRINCIPLES_REG" "$MATRIX_REG"
elif command -v agda >/dev/null 2>&1; then
  agda -i . "$PRINCIPLES_REG"
  agda -i . "$MATRIX_REG"
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "digital ESD transformative-principles source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi
