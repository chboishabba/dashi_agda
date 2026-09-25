{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact where

open import Agda.Builtin.Equality using (_≡_)

data Empty : Set where
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; _<ℝ_; *-comm)

------------------------------------------------------------------------
-- MINIMAL STRICT-ORDER ALGEBRA NEEDED BY THE REAL ANTIGRAVITY SOURCE LANE
--
-- The repository's RealAnalysisAxioms intentionally exposes only a weak ordered
-- ring fragment.  Strict product signs are standard real-field facts but are
-- not currently fields of that authority surface.  Keep the extra authority
-- explicit and generic rather than hiding it in a physics-specific postulate.
------------------------------------------------------------------------

record RealStrictSignLaws : Set₁ where
  field
    strictThenWeak :
      ∀ {left middle right} →
      left <ℝ middle →
      middle ≤ℝ right →
      left <ℝ right

    positiveTimesPositive :
      ∀ {left right} →
      0ℝ <ℝ left →
      0ℝ <ℝ right →
      0ℝ <ℝ left *ℝ right

    positiveTimesNegative :
      ∀ {positive negative} →
      0ℝ <ℝ positive →
      negative <ℝ 0ℝ →
      positive *ℝ negative <ℝ 0ℝ

    nonnegativeNonzeroPositive :
      ∀ {value} →
      0ℝ ≤ℝ value →
      (value ≡ 0ℝ → Empty) →
      0ℝ <ℝ value

open RealStrictSignLaws public

negativeTimesPositive :
  RealStrictSignLaws →
  ∀ {negative positive} →
  negative <ℝ 0ℝ →
  0ℝ <ℝ positive →
  negative *ℝ positive <ℝ 0ℝ
negativeTimesPositive laws {negative} {positive} hneg hpos =
  subst
    (λ value → value <ℝ 0ℝ)
    (*-comm positive negative)
    (positiveTimesNegative laws hpos hneg)

positiveSquare :
  RealStrictSignLaws →
  ∀ {value} →
  0ℝ <ℝ value →
  0ℝ <ℝ value *ℝ value
positiveSquare laws h =
  positiveTimesPositive laws h h
