module DASHI.Foundations.BishopFiniteWeightedSumOrderExact where

------------------------------------------------------------------------
-- FINITE WEIGHTED-SUM MONOTONICITY OVER THE PINNED BISHOP REALS
--
-- If leftWeight x <= rightWeight x and mass x is nonnegative for every item,
-- then the finite weighted sum preserves that order.  This is only a compiler
-- over vendor/bishop's already-proved order-compatible multiplication/addition.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)

import Real as BishopReal
import RealProperties as BishopProps

weightedSum :
  ∀ {A : Set} →
  (A → BishopReal.ℝ) →
  (A → BishopReal.ℝ) →
  List A → BishopReal.ℝ
weightedSum weight mass [] = BishopReal.0ℝ
weightedSum weight mass (x ∷ rest) =
  BishopReal._+_
    (BishopReal._*_ (weight x) (mass x))
    (weightedSum weight mass rest)

finiteWeightedSumMonotone :
  ∀ {A : Set}
    (leftWeight rightWeight mass : A → BishopReal.ℝ) →
    ((x : A) → BishopReal._≤_ (leftWeight x) (rightWeight x)) →
    ((x : A) → BishopReal.NonNegative (mass x)) →
    (items : List A) →
    BishopReal._≤_
      (weightedSum leftWeight mass items)
      (weightedSum rightWeight mass items)
finiteWeightedSumMonotone leftWeight rightWeight mass pointwise massNN [] =
  BishopProps.≤-refl
finiteWeightedSumMonotone leftWeight rightWeight mass pointwise massNN (x ∷ rest) =
  BishopProps.+-mono-≤
    (BishopProps.*-monoʳ-≤-nonNeg (pointwise x) (massNN x))
    (finiteWeightedSumMonotone
      leftWeight rightWeight mass pointwise massNN rest)
