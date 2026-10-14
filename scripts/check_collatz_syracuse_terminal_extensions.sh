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
grep -q 'noInfiniteSurvivorGivesDoubleNegatedDescent' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'record NatSearchMarkov' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'natSearchMarkovOwnedUnconditionally : Nat' DASHI/Analysis/CollatzSyracuseConstructiveSurvivorExtractionExact.agda
grep -q 'trailingZeroCertificatePaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'residualFrontierStrictnessGuardPaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'residualInverseLimitObstructionPaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'finiteSurvivorBarrierExtractionPaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'noInfiniteSurvivorDoubleNegationPaid' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'strictnessGuardDoesNotCreateUnboundedness' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'inverseLimitAbsenceDoesNotConstructDescent' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda
grep -q 'markovNotSilentlyOwned' DASHI/Analysis/CollatzSyracuseTerminalParityMaxCutExact.agda

echo 'collatz syracuse terminal extension static checks: PASS'
