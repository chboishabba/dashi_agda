#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Moonshine/Monster3BCyclotomicNormSeparationExact.agda"

required=(
  "module DASHI.Moonshine.Monster3BCyclotomicNormSeparationExact"
  "normZeroImpliesZero"
  "nonzeroValueImpliesNormNonzero"
  "nonzeroAmplitudeFromValue"
  "washington"
  "10.1007/978-1-4612-1934-7"
  "citationDoesNotCreateNormSeparation"
  "A005052"
  "oeisHasNormAuthority"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing cyclotomic norm-separation surface: $needle" >&2
    exit 1
  fi
done

if grep -Eq '(^|[^[:alnum:]_])(postulate|{-# OPTIONS --allow-unsolved-metas|TERMINATING|NON_TERMINATING)([^[:alnum:]_]|$)' "$OWNER"; then
  echo "trust escape found in cyclotomic norm-separation owner" >&2
  exit 1
fi

echo "monster 3B cyclotomic norm separation check: ok"
