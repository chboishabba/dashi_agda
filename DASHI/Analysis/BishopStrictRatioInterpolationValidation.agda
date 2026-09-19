module DASHI.Analysis.BishopStrictRatioInterpolationValidation where

open import Agda.Builtin.Sigma using (Σ)
open import Data.Product.Base using (_×_)

import Real as BishopReal

import DASHI.Analysis.BishopStrictRatioInterpolationExact as P

interpolationRegression :
  ∀ {ratio : BishopReal.ℝ} →
  BishopReal._≤_ BishopReal.0ℝ ratio →
  BishopReal._<_ ratio BishopReal.1ℝ →
  Σ BishopReal.ℝ (λ larger →
    BishopReal._<_ BishopReal.0ℝ larger ×
    BishopReal._<_ ratio larger ×
    BishopReal._<_ larger BishopReal.1ℝ)
interpolationRegression = P.interpolateStrictUnitRatio
