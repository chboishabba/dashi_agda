#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/ProofDebtRouterExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required proof-debt source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^routeDebt :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^sourceEstablishedAlignedDeferredIsCertificationDebt :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^sourceEstablishedAlignedDeferredIsNotMathematicalDebt :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^record SourceAlignedDeferredTheorem' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^ConditionalDevelopment :' DASHI/Core/ProofDebtRouterExact.agda
grep -q '^certifyDeferred :' DASHI/Core/ProofDebtRouterExact.agda

scripts/run_agda29_parallel_check.sh DASHI/Core/ProofDebtRouterExact.agda
