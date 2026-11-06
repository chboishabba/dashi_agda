{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalNegativeLogUniformCompactTailExact where

------------------------------------------------------------------------
-- SOURCE K04d-LOG: EFFECTIVE COMPACT-UNIFORM CONVERGENCE.
--
-- For fixed 0<r<1, one precision cutoff N(r,k) controls the literal
-- negative-log series L_B(x)=sum_{n>=0} x^(n+1)/(n+1)
-- SIMULTANEOUSLY at all original Bishop points 0<x<=r.
--
-- The majorant is the original pinned geometric series
--   |sourceNegativeLogTerm x n| <= r*r^n.
-- This is a source-value theorem, not an arbitrary uniform-approximation
-- hypothesis. It eliminates a necessary compact-uniform-value leaf
-- on the direct LOG composition route. It does NOT, alone, justify
-- differentiation of the infinite limit or exp(-L)=1-x.
--
-- Reuses vendor/bishop Sequence Cauchy, limit and closed order, and
-- existing original log monotonicity and geometric-majorant owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Nat.Base as N using (NonZero; _≤_; _≥_)
import Data.Nat.Properties as NP
open import Data.Product.Base using (proj₁; proj₂; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Analysis.BishopGeometricMajorantSeriesConvergenceExact as Geo
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as Uniform

sourceLogTermBoundOnPositiveCompact :
  (radius : R.ℝ) →
  (radiusPositive : R._<_ R.0ℝ radius) →
  (point : R.ℝ) →
  (pointPositive : R._<_ R.0ℝ point) →
  R._≤_ point radius →
  (n : Nat) →
  R._≤_
    (R.∣ Log.sourceNegativeLogTerm point n ∣)
    (Geo.scaledGeometricTerm radius radius n)
sourceLogTermBoundOnPositiveCompact radius radiusPositive point pointPositive inside n =
  RP.≤-respˡ-≃
    (RP.≃-symm
      (RP.nonNegx⇒∣x∣≃x
        (Log.sourceNegativeLogTermNonnegative
          point
          (RP.0≤x⇒nonNegx (RP.<⇒≤ pointPositive))
          n)))
    (RP.≤-trans
      (Log.sourceNegativeLogTermMonotone
        point radius
        (RP.0≤x⇒nonNegx (RP.<⇒≤ pointPositive))
        inside n)
      (RP.≤-respˡ-≃
        (RP.≃-symm
          (RP.nonNegx⇒∣x∣≃x
            (Log.sourceNegativeLogTermNonnegative
              radius
              (RP.0≤x⇒nonNegx (RP.<⇒≤ radiusPositive))
              n)))
        (Log.sourceNegativeLogAbsoluteBelowGeometric
          radius
          (RP.0≤x⇒nonNegx (RP.<⇒≤ radiusPositive))
          n)))

sourceLogUniformTailCutoff :
  (radius : R.ℝ) →
  (radiusPositive : R._<_ R.0ℝ radius) →
  (radiusBelowOne : R._<_ radius R.1ℝ) →
  (k : Nat) → .{{_ : NonZero k}} →
  Nat
sourceLogUniformTailCutoff radius positive belowOne k =
  suc (proj₁
    (Seq.cauchyConvergenceTest-if
      (Geo.scaledGeometricTerm radius radius)
      (Geo.scaledGeometricSeriesConvergent
        radius radius positive belowOne
        (RP.0≤x⇒nonNegx (RP.<⇒≤ positive)))
      k))

sourceLogUniformOrderedFiniteTail :
  (radius : R.ℝ) →
  (radiusPositive : R._<_ R.0ℝ radius) →
  (radiusBelowOne : R._<_ radius R.1ℝ) →
  (point : R.ℝ) →
  (pointPositive : R._<_ R.0ℝ point) →
  R._≤_ point radius →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≤ n →
  m ≥ sourceLogUniformTailCutoff radius radiusPositive radiusBelowOne k →
  n ≥ sourceLogUniformTailCutoff radius radiusPositive radiusBelowOne k →
  R._≤_
    (R.∣ Seq.∑ (Log.sourceNegativeLogTerm point) m n ∣)
    (Uniform.inversePrecision k)
sourceLogUniformOrderedFiniteTail
    radius positive belowOne point pointPositive inside k
    m n ordered mPast nPast =
  RP.≤-trans
    (Seq.∑-triangle-inequality
      (Log.sourceNegativeLogTerm point) m n ordered)
    (RP.≤-trans
      (Seq.∑-mono-≤
        (sourceLogTermBoundOnPositiveCompact
          radius positive point pointPositive inside)
        m n ordered)
      (RP.≤-trans
        (RP.x≤∣x∣
          {x = Seq.∑ (Geo.scaledGeometricTerm radius radius) m n})
        (proj₂
          (Seq.cauchyConvergenceTest-if
            (Geo.scaledGeometricTerm radius radius)
            (Geo.scaledGeometricSeriesConvergent
              radius radius positive belowOne
              (RP.0≤x⇒nonNegx (RP.<⇒≤ positive)))
            k)
          m n mPast nPast)))

sourceLogUniformFiniteTail :
  (radius : R.ℝ) →
  (radiusPositive : R._<_ R.0ℝ radius) →
  (radiusBelowOne : R._<_ radius R.1ℝ) →
  (point : R.ℝ) →
  (pointPositive : R._<_ R.0ℝ point) →
  R._≤_ point radius →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≥ sourceLogUniformTailCutoff radius radiusPositive radiusBelowOne k →
  n ≥ sourceLogUniformTailCutoff radius radiusPositive radiusBelowOne k →
  R._≤_
    (R.∣ Seq.∑ (Log.sourceNegativeLogTerm point) m n ∣)
    (Uniform.inversePrecision k)
sourceLogUniformFiniteTail
    radius positive belowOne point pointPositive inside k
    m n mPast nPast with NP.≤-total m n
... | inj₁ ordered =
  sourceLogUniformOrderedFiniteTail
    radius positive belowOne point pointPositive inside k
    m n ordered mPast nPast
... | inj₂ ordered =
  RP.≤-respˡ-≃
    (RP.≃-trans
      (RP.≃-symm
        (RP.∣-x∣≃∣x∣
          {x = Seq.∑ (Log.sourceNegativeLogTerm point) m n}))
      (RP.∣-∣-cong
        (Seq.neg-flips-∑
          (Log.sourceNegativeLogTerm point) m n)))
    (sourceLogUniformOrderedFiniteTail
      radius positive belowOne point pointPositive inside k
      n m ordered nPast mPast)

sourceLogFinitePartialMinusIsTail :
  (point : R.ℝ) (m n : Nat) →
  R._≃_
    (R._-_
      (Seq.SeriesOf (Log.sourceNegativeLogTerm point) n)
      (Seq.SeriesOf (Log.sourceNegativeLogTerm point) m))
    (Seq.∑ (Log.sourceNegativeLogTerm point) m n)
sourceLogFinitePartialMinusIsTail point zero n =
  let open RP.ℝ-Solver in
  solve 1
    (λ prefix → prefix ⊖ Κ 0ℚᵘ ⊜ prefix)
    RP.≃-refl (Seq.SeriesOf (Log.sourceNegativeLogTerm point) n)
sourceLogFinitePartialMinusIsTail point (suc m) n =
  RP.≃-refl

sourceLogUniformLimitError :
  (radius : R.ℝ) →
  (radiusPositive : R._<_ R.0ℝ radius) →
  (radiusBelowOne : R._<_ radius R.1ℝ) →
  (point : R.ℝ) →
  (pointPositive : R._<_ R.0ℝ point) →
  (pointBelowOne : R._<_ point R.1ℝ) →
  R._≤_ point radius →
  (k : Nat) → .{{_ : NonZero k}} →
  (m : Nat) →
  m ≥ sourceLogUniformTailCutoff radius radiusPositive radiusBelowOne k →
  R._≤_
    (R.∣
      R._-_
        (Log.sourceNegativeLogValue point pointPositive pointBelowOne)
        (Seq.SeriesOf (Log.sourceNegativeLogTerm point) m)
    ∣)
    (Uniform.inversePrecision k)
sourceLogUniformLimitError
    radius positive belowOne point pointPositive pointBelowOne inside
    k m mPast =
  let
    cutoff = sourceLogUniformTailCutoff radius positive belowOne k
    partial = Seq.SeriesOf (Log.sourceNegativeLogTerm point)
    limit = Log.sourceNegativeLogValue point pointPositive pointBelowOne
    converges = Log.sourceNegativeLogValueConverges
      point pointPositive pointBelowOne

    shifted : Nat → R.ℝ
    shifted n = partial (n + cutoff)

    shiftedConverges : Seq._ConvergesTo_ shifted limit
    shiftedConverges =
      Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
        (Seq.subseq*
          ((λ n → n + cutoff)
          , (λ n → RP.≃-refl)
          , (λ n → NP.n<1+n (n + cutoff))))
        (limit , converges)

    negPartialConverges : Seq._isConvergent
      (λ _ → R.-_ (partial m))
    negPartialConverges =
      R.-_ (partial m) ,
      Seq.xₙ≃c⇒xₙ→c (λ {(suc n) → RP.≃-refl})

    differenceConverges :
      Seq._ConvergesTo_
        (λ n → R._-_ (shifted n) (partial m))
        (R._-_ limit (partial m))
    differenceConverges =
      Seq.xₙ+yₙ→x₀+y₀
        (limit , shiftedConverges)
        negPartialConverges

    absConvergent : Seq._isConvergent
      (λ n → R.∣ R._-_ (shifted n) (partial m) ∣)
    absConvergent =
      R.∣ R._-_ limit (partial m) ∣ ,
      Seq.∣xₙ∣→∣x₀∣
        (R._-_ limit (partial m) , differenceConverges)

    boundEach : (n : Nat) →
      R._≤_
        (R.∣ R._-_ (shifted n) (partial m) ∣)
        (Uniform.inversePrecision k)
    boundEach n =
      RP.≤-respˡ-≃
        (RP.∣-∣-cong
          (sourceLogFinitePartialMinusIsTail
            point m (n + cutoff)))
        (sourceLogUniformFiniteTail
          radius positive belowOne point pointPositive inside k
          m (n + cutoff)
          mPast (NP.m≤n+m cutoff n))
  in
  Seq.xₙ≤y⇒limxₙ≤y boundEach absConvergent

-- One common original majorant cutoff, all 0<x<=r points.
originalNegativeLogUniformApproximation :
  (radius : R.ℝ) →
  (radiusPositive : R._<_ R.0ℝ radius) →
  (radiusBelowOne : R._<_ radius R.1ℝ) →
  (k : Nat) → .{{_ : NonZero k}} →
  (point : R.ℝ) →
  (pointPositive : R._<_ R.0ℝ point) →
  (pointBelowOne : R._<_ point R.1ℝ) →
  R._≤_ point radius →
  R._≤_
    (R.∣
      R._-_
        (Seq.SeriesOf (Log.sourceNegativeLogTerm point)
          (sourceLogUniformTailCutoff radius radiusPositive radiusBelowOne k))
        (Log.sourceNegativeLogValue point pointPositive pointBelowOne)
    ∣)
    (Uniform.inversePrecision k)
originalNegativeLogUniformApproximation
    radius positive belowOne k point pointPositive pointBelowOne inside =
  RP.≤-respˡ-≃
    (RP.∣x-y∣≃∣y-x∣
      (Log.sourceNegativeLogValue point pointPositive pointBelowOne)
      (Seq.SeriesOf (Log.sourceNegativeLogTerm point)
        (sourceLogUniformTailCutoff radius positive belowOne k)))
    (sourceLogUniformLimitError
      radius positive belowOne point pointPositive pointBelowOne inside
      k (sourceLogUniformTailCutoff radius positive belowOne k)
      NP.≤-refl)
