module DASHI.Analysis.RiemannImprovedZeroFreeG21UniformGapRegression where

import DASHI.Analysis.RiemannImprovedZeroFreeG21UniformGapExact as Gap

open import DASHI.Core.Prelude

regressionHalfGapNumerator :
  Gap.safeAlphaNumerator + Gap.safePoleGapNumerator ≡ Gap.halfNumerator
regressionHalfGapNumerator = Gap.safeAlphaPlusPoleGapIsHalf

regressionGapStrictlyExceedsOneEighth :
  8 * Gap.safePoleGapNumerator ≡ Gap.safeDenominator + 168
regressionGapStrictlyExceedsOneEighth =
  Gap.safePoleGapStrictlyExceedsOneEighthCrossProduct

regressionUniformGapAvailableConditionally :
  Gap.G21UniformPoleGapBoundary.uniformPositivePoleGapCompilerConstructed
    Gap.canonicalG21UniformPoleGapBoundary ≡ true
regressionUniformGapAvailableConditionally =
  Gap.G21UniformPoleGapBoundary.uniformPositivePoleGapCompilerConstructedIsTrue
    Gap.canonicalG21UniformPoleGapBoundary

regressionParityMinorStillOpen :
  Gap.G21UniformPoleGapBoundary.actualParityMinorDerived
    Gap.canonicalG21UniformPoleGapBoundary ≡ false
regressionParityMinorStillOpen =
  Gap.G21UniformPoleGapBoundary.actualParityMinorDerivedIsFalse
    Gap.canonicalG21UniformPoleGapBoundary
