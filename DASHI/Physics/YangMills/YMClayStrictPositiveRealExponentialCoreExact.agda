module DASHI.Physics.YangMills.YMClayStrictPositiveRealExponentialCoreExact where

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

record StrictPositiveRealExponential : Set₁ where
  field
    expReal : ℝ → ℝ
    expPositive :
      ∀ value →
      0ℝ <ℝ expReal value

open StrictPositiveRealExponential public
