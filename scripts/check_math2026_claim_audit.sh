#!/usr/bin/env bash
set -euo pipefail

ROOT="DASHI/Math2026ClaimAuditValidation.agda"
FILES=(
  DASHI/Analysis/DeBruijnNewman2026ClaimAuditExact.agda
  DASHI/Mathematics/NumberTheory/PrimeGap2026ClaimAuditExact.agda
  DASHI/Mathematics/NumberTheory/DiophantineTupleDPrimeSquare2026ClaimAuditExact.agda
  DASHI/Core/ExternalAutoformalizationProvenanceExact.agda
  "$ROOT"
)

if grep -nE '\b(postulate|{-# OPTIONS --allow-unsolved-metas #-}|\?|{!!})\b' "${FILES[@]}"; then
  echo "unsafe or incomplete proof surface found" >&2
  exit 1
fi

if command -v agda >/dev/null 2>&1; then
  agda -i . "$ROOT"
else
  echo "agda not available; trust scan only"
fi
