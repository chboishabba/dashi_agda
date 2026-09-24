#!/usr/bin/env bash
set -euo pipefail

files=(
  DASHI/Physics/Closure/DrellYanRatioAbsoluteDefectLocalizationExact.agda
  DASHI/Physics/Closure/DrellYanRatioAbsoluteDefectLocalizationValidation.agda
  DASHI/Physics/Closure/ColliderChiSquareScopeMatrixExact.agda
  DASHI/Physics/Closure/ColliderChiSquareScopeMatrixValidation.agda
  DASHI/Physics/Foundations/CMP119PinnedYMGRQFTSectorStressBridgeExact.agda
  DASHI/Physics/Foundations/CMP119PinnedYMGRQFTSectorStressBridgeValidation.agda
  DASHI/Physics/Foundations/GRQFTPostMergeMaxCutExact.agda
  DASHI/Physics/Foundations/GRQFTPostMergeMaxCutValidation.agda
)

for f in "${files[@]}"; do
  test -f "$f"
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)' "$f"; then
    echo "forbidden trust/hole pattern in $f" >&2
    exit 1
  fi
done

tmp1="$(mktemp)"
tmp2="$(mktemp)"
trap 'rm -f "$tmp1" "$tmp2"' EXIT
python3 scripts/grqft_dy_ratio_absolute_localization.py --output "$tmp1" >/dev/null
diff -u outputs/grqft_dy_ratio_absolute_localization.json "$tmp1"
python3 scripts/grqft_collider_chi2_scope_matrix.py --output "$tmp2" >/dev/null
diff -u outputs/grqft_collider_chi2_scope_matrix.json "$tmp2"

if command -v dashi-agda-preflight >/dev/null 2>&1; then
  for f in "${files[@]}"; do
    dashi-agda-preflight "$f"
  done
fi
