#!/usr/bin/env bash
set -euo pipefail

files=(
  DASHI/Analysis/RiemannAristotleSharedWindowCertificateExact.agda
  DASHI/Analysis/CertifiedFiniteCarrierReindexExact.agda
  DASHI/Analysis/RiemannAristotleSharedCertificateReturnExact.agda
  DASHI/Analysis/RiemannAristotleSharedCertificateReturnRegression.agda
  DASHI/Analysis/RiemannAristotleWindowSchurCrossProverRegression.agda
)

if grep -nE '\b(postulate|{-# COMPILE|{-# FOREIGN)\b' "${files[@]}"; then
  echo "trust scan failed" >&2
  exit 1
fi

if [[ -x scripts/run_agda_pinned.sh ]]; then
  scripts/run_agda_pinned.sh DASHI/Analysis/RiemannAristotleSharedCertificateReturnRegression.agda
  scripts/run_agda_pinned.sh DASHI/Analysis/RiemannAristotleWindowSchurCrossProverRegression.agda
else
  echo "pinned Agda driver unavailable" >&2
  exit 2
fi
