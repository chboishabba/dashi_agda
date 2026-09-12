#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Moonshine/Monster3BFiniteSchrodingerNonzeroWitnessExtractionExact.agda"

required=(
  "module DASHI.Moonshine.Monster3BFiniteSchrodingerNonzeroWitnessExtractionExact"
  "data CubeSearchResult"
  "searchTritCube"
  "record OrdinaryNonzeroInvariantVector"
  "upgradeOrdinaryNonzeroInvariantVector"
  "ordinaryNonzeroInvariantSubspaceIsWholeCarrier"
  "nonzeroValueImpliesNormNonzero"
  "A005052"
  "oeisHasWitnessAuthority"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing Schrodinger nonzero-witness extraction surface: $needle" >&2
    exit 1
  fi
done

if grep -Eq '(^|[^[:alnum:]_])(postulate|{-# OPTIONS --allow-unsolved-metas|TERMINATING|NON_TERMINATING)([^[:alnum:]_]|$)' "$OWNER"; then
  echo "trust escape found in Schrodinger nonzero-witness extraction owner" >&2
  exit 1
fi

echo "monster 3B Schrodinger nonzero-witness extraction check: ok"
