#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/NumberTheory/Collatz/SyracuseExact.agda"
[[ -f "$owner" ]]

grep -q 'record PositiveNat' "$owner"
grep -q 'parityBool' "$owner"
grep -q 'shortcutSyracuse' "$owner"
grep -q 'syracuseIterate' "$owner"
grep -q 'shortcutSyracusePositive' "$owner"
grep -q 'shortcutIndexParityFalse' "$owner"
grep -q 'shortcutIndexParityTrue' "$owner"
grep -q 'shortcutSyracuseParityFalse' "$owner"
grep -q 'shortcutSyracuseParityTrue' "$owner"
grep -q 'syracuseIterateSuc' "$owner"

! grep -q 'postulate' "$owner"
! grep -q '{!!}' "$owner"
! grep -q 'OPTIONS --allow-unsolved-metas' "$owner"
! grep -Eq '= *\?' "$owner"

echo 'collatz syracuse exact static checks: PASS'
