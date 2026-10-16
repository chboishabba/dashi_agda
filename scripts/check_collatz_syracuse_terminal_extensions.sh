#!/usr/bin/env bash
set -euo pipefail

files=(
  DASHI/Analysis/CollatzSyracuseUniformWordDescentCertificateExact.agda
  DASHI/Analysis/CollatzSyracuseTrailingZeroCertificateExact.agda
  DASHI/Analysis/CollatzSyracuseTrailingZeroCertificateValidation.agda
  DASHI/Analysis/CollatzSyracuseResidualWordCertificateFrontierExact.agda
  DASHI/Analysis/CollatzSyracuseResidualFrontierStrictnessGuardExact.agda
  DASHI/Analysis/CollatzSyracuseResidualFrontierStrictnessGuardValidation.agda
  DASHI/Analysis/CollatzSyracuseResidualInverseLimitObstructionExact.agda
  DASHI/Analysis/CollatzSyracuseResidualInverseLimitObstructionValidation.agda
  DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
  DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionValidation.agda
  DASHI/Analysis/CollatzSyracuseSOTA2026Exact.agda
  DASHI/Analysis/CollatzSyracuseSOTA2026Validation.agda
  DASHI/Analysis/CollatzSyracuseParadoxicalPrefixExact.agda
  DASHI/Analysis/CollatzSyracuseParadoxicalPrefixValidation.agda
  DASHI/Analysis/CollatzSyracuseCoefficientResonanceExact.agda
  DASHI/Analysis/CollatzSyracuseCoefficientResonanceValidation.agda
  DASHI/Analysis/CollatzSyracuseContractingWordFamilyExact.agda
  DASHI/Analysis/CollatzSyracuseContractingWordFamilyValidation.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdExact.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdValidation.agda
  DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionExact.agda
  DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionValidation.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierTransitionExact.agda
  DASHI/Analysis/CollatzSyracuseSharpBarrierTransitionValidation.agda
  DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryExact.agda
  DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryValidation.agda
  DASHI/Analysis/CollatzSyracuseInfiniteSurvivorAffineObstructionExact.agda
  DASHI/Analysis/CollatzSyracuseInfiniteSurvivorAffineObstructionValidation.agda
  DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
  DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutValidation.agda
)

for file in "${files[@]}"; do
  [[ -f "$file" ]]
  ! grep -q 'postulate' "$file"
  ! grep -q '{!!}' "$file"
  ! grep -q 'OPTIONS --allow-unsolved-metas' "$file"
  ! grep -Eq '= *\?' "$file"
done

grep -q 'appendZeroCertificate' DASHI/Analysis/CollatzSyracuseTrailingZeroCertificateExact.agda
grep -q 'appendZerosCertificate' DASHI/Analysis/CollatzSyracuseTrailingZeroCertificateExact.agda
grep -q 'trailingZeroCompilerCreatesUniversalStopping : Nat' DASHI/Analysis/CollatzSyracuseTrailingZeroCertificateExact.agda
grep -q 'globallyBoundedFrontierCannotCoverHighResidual' DASHI/Analysis/CollatzSyracuseResidualFrontierStrictnessGuardExact.agda
grep -q 'wordCertificateFrontierCannotBeGloballyBounded' DASHI/Analysis/CollatzSyracuseResidualFrontierStrictnessGuardExact.agda
grep -q 'finiteCoverageCreatesUnboundedness : Nat' DASHI/Analysis/CollatzSyracuseResidualFrontierStrictnessGuardExact.agda
grep -q 'inversePointFromAllHorizon' DASHI/Analysis/CollatzSyracuseResidualInverseLimitObstructionExact.agda
grep -q 'allHorizonFromInversePoint' DASHI/Analysis/CollatzSyracuseResidualInverseLimitObstructionExact.agda
grep -q 'infiniteSurvivorRefutesStrictDescent' DASHI/Analysis/CollatzSyracuseResidualInverseLimitObstructionExact.agda
grep -q 'universalStoppingExcludesInfiniteSurvivor' DASHI/Analysis/CollatzSyracuseResidualInverseLimitObstructionExact.agda
grep -q 'noInverseLimitAutomaticallyConstructsDescent : Nat' DASHI/Analysis/CollatzSyracuseResidualInverseLimitObstructionExact.agda
grep -q 'finiteBarrierExtractsDescent' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'finiteBarrierToLiteralStrictDescentSource' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'literalStrictDescentToFiniteBarrierSource' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'record FiniteBarrierStrictDescentEquivalence' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'finiteBarrierStrictDescentEquivalencePaid : Nat' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'noInfiniteSurvivorGivesDoubleNegatedDescent' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'noInversePointGivesDoubleNegatedDescent' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'strictDescentFromNoInversePointWithMarkov' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'record NatSearchMarkov' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'natSearchMarkovOwnedUnconditionally : Nat' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda

grep -q 'collatzSOTA2026Atlas' DASHI/Analysis/CollatzSyracuseSOTA2026Exact.agda
grep -q 'coefficientStoppingHistoryAttributed : Nat' DASHI/Analysis/CollatzSyracuseSOTA2026Exact.agda
grep -q 'binaryTernaryAutomatonRoleSeparated : Nat' DASHI/Analysis/CollatzSyracuseSOTA2026Exact.agda
grep -q 'semiconvergentPassageTheoremRoleSeparated : Nat' DASHI/Analysis/CollatzSyracuseSOTA2026Exact.agda
grep -q 'coefficientStoppingConjecturePromotedToProof : Nat' DASHI/Analysis/CollatzSyracuseSOTA2026Exact.agda
grep -q 'paradoxicalPrefixForcesCorrectionDominance' DASHI/Analysis/CollatzSyracuseParadoxicalPrefixExact.agda
grep -q 'paradoxicalPrefixStartBoundedByCorrection' DASHI/Analysis/CollatzSyracuseParadoxicalPrefixExact.agda
grep -q 'sameCountDifferentCorrection' DASHI/Analysis/CollatzSyracuseParadoxicalPrefixExact.agda
grep -q 'sameOddCountSameThreePower' DASHI/Analysis/CollatzSyracuseCoefficientResonanceExact.agda
grep -q 'record ExactNearResonanceCertificate' DASHI/Analysis/CollatzSyracuseCoefficientResonanceExact.agda
grep -q 'canonicalContractingWordCertificate' DASHI/Analysis/CollatzSyracuseContractingWordFamilyExact.agda
grep -q 'contractingWordFamilyDescends' DASHI/Analysis/CollatzSyracuseContractingWordFamilyExact.agda

grep -q 'sharpThreshold' DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdExact.agda
grep -q 'sharpThresholdIsMinimalUniformAffineThreshold' DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdExact.agda
grep -q 'paradoxicalStartAtMostQuotientBarrier' DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdExact.agda
grep -q 'sharp11010Threshold' DASHI/Analysis/CollatzSyracuseSharpBarrierThresholdExact.agda
grep -q 'affineTermAppendOne' DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionExact.agda
grep -q 'classifyOddGapRegime' DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionExact.agda
grep -q 'appendOneContractingCoefficient' DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionExact.agda
grep -q 'oddExtendedGap word coefficient' DASHI/Analysis/CollatzSyracuseAffinePrefixTransitionExact.agda
grep -q 'trailingEvenSharpThresholdNonincreasing' DASHI/Analysis/CollatzSyracuseSharpBarrierTransitionExact.agda
grep -q 'arbitraryTrailingEvenSharpThresholdNonincreasing' DASHI/Analysis/CollatzSyracuseSharpBarrierTransitionExact.agda

grep -q 'descentImpliesCoefficientContracts' DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryExact.agda
grep -q 'coefficientHorizonAtMostDescentHorizon' DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryExact.agda
grep -q 'correctionFitAtCoefficientHorizonImpliesEquality' DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryExact.agda
grep -q 'universalCoefficientStoppingEqualityPaid : Nat' DASHI/Analysis/CollatzSyracuseCoefficientStoppingBoundaryExact.agda

grep -q 'contractingSurvivorForcesCorrectionDominance' DASHI/Analysis/CollatzSyracuseInfiniteSurvivorAffineObstructionExact.agda
grep -q 'oneContractingCorrectionFitRefutesInfiniteSurvivor' DASHI/Analysis/CollatzSyracuseInfiniteSurvivorAffineObstructionExact.agda
grep -q 'universalContractingCorrectionEscapeProducerPaid : Nat' DASHI/Analysis/CollatzSyracuseInfiniteSurvivorAffineObstructionExact.agda

grep -q 'sharpBarrierThresholdPaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'sharpBarrierMinimalityPaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'affinePrefixTransitionPaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'safeOddGapProducerPaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'trailingEvenSharpBarrierMonotonicityPaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'contractingCorrectionEscapeStillOpen' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'inverseLimitAbsenceDoesNotConstructDescent' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'markovNotSilentlyOwned' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda

python3 scripts/check_collatz_syracuse_residual_resonance.py >/dev/null
python3 scripts/check_collatz_syracuse_sharp_barrier.py >/dev/null

echo 'collatz syracuse terminal extension static checks: PASS'
