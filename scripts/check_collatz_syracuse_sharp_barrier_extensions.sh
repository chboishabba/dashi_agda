#!/usr/bin/env bash
set -euo pipefail

files=(
  DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdExact.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdValidation.agda
  DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionExact.agda
  DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionValidation.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierTransitionExact.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierTransitionValidation.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierOneZeroTransitionExact.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierOneZeroTransitionValidation.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierPrimitiveASTExact.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierPrimitiveASTValidation.agda
  DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryExact.agda
  DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryValidation.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierTerminalMaxCutExact.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierTerminalMaxCutValidation.agda
)

for file in "${files[@]}"; do
  [[ -f "$file" ]]
  ! grep -q 'postulate' "$file"
  ! grep -q '{!!}' "$file"
  ! grep -q 'OPTIONS --allow-unsolved-metas' "$file"
  ! grep -Eq '= *\?' "$file"
done

grep -q 'sharpThresholdIsMinimalUniformAffineThreshold' DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdExact.agda
grep -q 'paradoxicalStartAtMostQuotientBarrier' DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdExact.agda
grep -q 'appendOneContractingCoefficient' DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionExact.agda
grep -q 'oddExtendedGap word coefficient' DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionExact.agda
grep -q 'arbitraryTrailingEvenSharpThresholdNonincreasing' DASHI/Analysis/CollatzSyracuseSharpBarrierTransitionExact.agda
grep -q 'appendOneZeroContractingCoefficient' DASHI/Analysis/CollatzSyracuseSharpBarrierOneZeroTransitionExact.agda
grep -q 'trailingOneZeroSharpThresholdNonincreasing' DASHI/Analysis/CollatzSyracuseSharpBarrierOneZeroTransitionExact.agda

grep -q 'data PrimitiveStep : Nat → Nat → Set' DASHI/Analysis/CollatzSyracuseSharpBarrierPrimitiveASTExact.agda
grep -q 'data PrimitiveAST : Nat → Nat → Set' DASHI/Analysis/CollatzSyracuseSharpBarrierPrimitiveASTExact.agda
grep -q 'record ActualCertifiedPath' DASHI/Analysis/CollatzSyracuseSharpBarrierPrimitiveASTExact.agda
grep -q 'record UniversalASTBarrierEscapeSource' DASHI/Analysis/CollatzSyracuseSharpBarrierPrimitiveASTExact.agda
grep -q 'astEscapeCompilesToCanonical' DASHI/Analysis/CollatzSyracuseSharpBarrierPrimitiveASTExact.agda
grep -q 'canonicalEscapeCompilesToASTPaid : Nat' DASHI/Analysis/CollatzSyracuseSharpBarrierPrimitiveASTExact.agda
grep -q 'universalBarrierEscapeProducerPaid : Nat' DASHI/Analysis/CollatzSyracuseSharpBarrierPrimitiveASTExact.agda

grep -q 'coefficientHorizonAtMostDescentHorizon' DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryExact.agda
grep -q 'correctionFitAtCoefficientHorizonImpliesEquality' DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryExact.agda
grep -q 'universalCoefficientStoppingEqualityPaid : Nat' DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryExact.agda
grep -q 'universalASTBarrierEscapeStillOpen' DASHI/Analysis/CollatzSyracuseSharpBarrierTerminalMaxCutExact.agda
grep -q 'universalCorrectionEscapeStillOpen' DASHI/Analysis/CollatzSyracuseSharpBarrierTerminalMaxCutExact.agda
grep -q 'universalCoefficientStoppingStillOpen' DASHI/Analysis/CollatzSyracuseSharpBarrierTerminalMaxCutExact.agda

python3 scripts/check_collatz_syracuse_sharp_barrier.py >/dev/null

echo 'collatz syracuse sharp-barrier capstone static checks: PASS'
