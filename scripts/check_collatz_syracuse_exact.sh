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
  DASHI/Core/BinaryWordIntegerChernoffExact.agda
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
  DASHI/NumberTheory/Collatz/SyracuseAffineCorrectionBoundExact.agda
  DASHI/Analysis/CollatzSyracuseCompleteBlockBijectionExact.agda
  DASHI/Analysis/CollatzSyracuseAlignedBlockUniformityExact.agda
  DASHI/Analysis/CollatzSyracuseParityBernoulliExact.agda
  DASHI/Analysis/CollatzSyracuseParityDescentEventExact.agda
  DASHI/Analysis/CollatzSyracuseFiveEightTailExact.agda
  DASHI/Analysis/CollatzSyracuseAlignedBlockDescentExact.agda
  DASHI/Analysis/CollatzSyracuseAlignedBlockTailExact.agda
  DASHI/Analysis/CollatzSyracuseHoeffdingMathlibBoundaryExact.agda
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
grep -q 'alignedBlockUniformWordMass' \
  DASHI/Analysis/CollatzSyracuseAlignedBlockUniformityExact.agda
grep -q 'canonicalCompleteBlockParityWordLaw' \
  DASHI/Analysis/CollatzSyracuseParityBernoulliExact.agda
grep -q 'strictAffineMarginImpliesDescent' \
  DASHI/NumberTheory/Collatz/SyracuseAffineDescentMarginExact.agda
grep -q 'coarseParityMarginImpliesDescent' \
  DASHI/NumberTheory/Collatz/SyracuseAffineCorrectionBoundExact.agda
grep -q 'integerChernoff' \
  DASHI/Core/BinaryWordIntegerChernoffExact.agda
grep -q 'badWordCount' \
  DASHI/Analysis/CollatzSyracuseParityDescentEventExact.agda
grep -q 'fiveEightBadWordBound' \
  DASHI/Analysis/CollatzSyracuseFiveEightTailExact.agda
grep -q 'nonDescentImpliesBadWord' \
  DASHI/Analysis/CollatzSyracuseAlignedBlockDescentExact.agda
grep -q 'alignedBlockFiveEightNonDescentBound' \
  DASHI/Analysis/CollatzSyracuseAlignedBlockTailExact.agda
grep -q 'cutStatus C12c-exponentialBadWordTail = proved' \
  DASHI/Analysis/CollatzSyracuseSameObjectMaxCutExact.agda
grep -q 'cutStatus C13a-alignedBlockLiteralDescent = proved' \
  DASHI/Analysis/CollatzSyracuseSameObjectMaxCutExact.agda
grep -q 'cutStatus C13b-alignedBlockFiniteTail = proved' \
  DASHI/Analysis/CollatzSyracuseSameObjectMaxCutExact.agda

echo 'collatz syracuse exact static checks: PASS'
