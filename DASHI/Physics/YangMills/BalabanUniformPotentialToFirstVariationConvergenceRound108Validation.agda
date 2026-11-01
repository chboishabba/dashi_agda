{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUniformPotentialToFirstVariationConvergenceRound108Validation where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)

import DASHI.Physics.YangMills.BalabanUniformPotentialToFirstVariationConvergenceRound108Exact as R108

firstVariationUsesPotentialModulus :
  R108.NormalizedCauchyDerivativeConvergence → ℚ → Nat
firstVariationUsesPotentialModulus = R108.firstVariationConvergenceModulus

firstVariationConvergesWithSameModulus :
  (dataSet : R108.NormalizedCauchyDerivativeConvergence) →
  ∀ tolerance →
  0ℚ < tolerance →
  ∀ n → R108.firstVariationConvergenceModulus dataSet tolerance ≤ n →
  R108.firstVariationError dataSet n < tolerance
firstVariationConvergesWithSameModulus = R108.firstVariationEventuallyBelow
