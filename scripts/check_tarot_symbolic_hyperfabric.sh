#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Biology/TarotCarrierExact.agda
  DASHI/Biology/TarotSemanticKernelExact.agda
  DASHI/Biology/TarotSpreadHyperfabricExact.agda
  DASHI/Biology/TarotInterpretationPNFExact.agda
  DASHI/Biology/TarotSourceAtlas.agda
  DASHI/Biology/TarotRegression.agda
  DASHI/Biology/TarotEverything.agda
  DASHI/Biology/TarotValidation.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required tarot formalisation source is missing: $file" >&2
    exit 1
  fi

  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

semantic_clause_count="$(
  grep -c '^meaning (Tarot\.' DASHI/Biology/TarotSemanticKernelExact.agda
)"
if [[ "$semantic_clause_count" -ne 78 ]]; then
  echo "expected 78 total card-meaning clauses, found $semantic_clause_count" >&2
  exit 1
fi

grep -q 'riderWaiteSmithDeckCountIsSeventyEight' \
  DASHI/Biology/TarotCarrierExact.agda
grep -q 'canonicalThreeDrawsAreDistinct' \
  DASHI/Biology/TarotSpreadHyperfabricExact.agda
grep -q 'canonicalSpreadObstruction' \
  DASHI/Biology/TarotSpreadHyperfabricExact.agda
grep -q 'canonicalReflectiveTraceCompilesWithoutExternalPrediction' \
  DASHI/Biology/TarotInterpretationPNFExact.agda
grep -q 'retainedAlternativeNarratives' \
  DASHI/Biology/TarotInterpretationPNFExact.agda
grep -q 'futureCausationProved : Bool' \
  DASHI/Biology/TarotInterpretationPNFExact.agda
grep -q 'clinicalDiagnosisAuthorised : Bool' \
  DASHI/Biology/TarotInterpretationPNFExact.agda
grep -q 'fixedOutcomeIsNotReflectiveIntervention' \
  DASHI/Biology/TarotInterpretationPNFExact.agda
grep -q 'DOI 10.48550/arXiv.2602.11367' \
  DASHI/Biology/TarotSourceAtlas.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/TarotRegression.agda \
  DASHI/Biology/TarotEverything.agda \
  DASHI/Biology/TarotValidation.agda
