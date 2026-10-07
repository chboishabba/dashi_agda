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

formal_files=(
  DASHI/NumberTheory/Collatz/SyracuseExact.agda
  DASHI/NumberTheory/Collatz/SyracuseParityItineraryExact.agda
  DASHI/NumberTheory/Collatz/SyracusePow2ArithmeticExact.agda
  DASHI/NumberTheory/Collatz/SyracuseOneStepArithmeticExact.agda
  DASHI/NumberTheory/Collatz/SyracuseParityCylinderCandidateExact.agda
  DASHI/NumberTheory/Collatz/SyracuseInv3Pow2Exact.agda
  DASHI/NumberTheory/Collatz/SyracuseNatModCongruenceExact.agda
  DASHI/NumberTheory/Collatz/SyracuseParityCylinderEvenBranchExact.agda
  DASHI/NumberTheory/Collatz/SyracuseParityCylinderRepresentativeExact.agda
  DASHI/NumberTheory/Collatz/SyracuseParityCylinderCompilerExact.agda
  DASHI/NumberTheory/Collatz/SyracuseParityCylinderOneStepBaseExact.agda
  DASHI/NumberTheory/Collatz/SyracuseParityCylinderOddResidualExact.agda
  DASHI/NumberTheory/Collatz/SyracuseParityCylinderOddBranchExact.agda
  DASHI/NumberTheory/Collatz/SyracuseAffineIterateExact.agda
  DASHI/NumberTheory/Collatz/SyracuseAffineIterateCompilerExact.agda
  DASHI/NumberTheory/Collatz/SyracuseAffineDescentMarginExact.agda
  DASHI/Analysis/CollatzSyracuseCompleteBlockBijectionExact.agda
  DASHI/Analysis/CollatzSyracuseParityBernoulliExact.agda
  DASHI/Analysis/CollatzSyracuseSameObjectMaxCutExact.agda
)

for file in "${formal_files[@]}"; do
  [[ -f "$file" ]]
  ! grep -q 'postulate' "$file"
  ! grep -q '{!!}' "$file"
  ! grep -q 'OPTIONS --allow-unsolved-metas' "$file"
  ! grep -Eq '= *\?' "$file"
done

grep -q 'canonicalParityCylinderSource' \
  DASHI/NumberTheory/Collatz/SyracuseParityCylinderOddBranchExact.agda
grep -q 'canonicalCompleteBlockUniformWordMass' \
  DASHI/Analysis/CollatzSyracuseCompleteBlockBijectionExact.agda
grep -q 'canonicalCompleteBlockParityWordLaw' \
  DASHI/Analysis/CollatzSyracuseParityBernoulliExact.agda
grep -q 'strictAffineMarginImpliesDescent' \
  DASHI/NumberTheory/Collatz/SyracuseAffineDescentMarginExact.agda

echo 'collatz syracuse exact static checks: PASS'
