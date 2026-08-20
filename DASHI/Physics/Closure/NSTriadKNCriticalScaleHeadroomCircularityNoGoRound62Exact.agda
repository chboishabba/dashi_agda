module DASHI.Physics.Closure.NSTriadKNCriticalScaleHeadroomCircularityNoGoRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 62 CIRCULARITY FALSIFIER
--
-- The fixed-shift block headroom is
--
--   A_n + B_* X_n <= gap T_n,
--
-- with A_n>=0 and B_*>0.  It is tempting to recycle this inequality to prove
-- the missing C critical-scale estimate.  But the strongest estimate obtainable
-- from headroom and A_n>=0 alone is
--
--   X_n <= (gap/B_*) T_n.
--
-- If this recycled coefficient K=gap/B_* is fed back into C's required strict
-- coefficient inequality
--
--   a + B_* K <= gap,
--
-- then exact algebra gives
--
--   a + gap <= gap,
--
-- hence a<=0.  For any positive additive data scale a>0 this is impossible.
--
-- Therefore the physical estimate X_n<=K T_n used to create B_* MUST be proved
-- upstream and independently of the final owner correction headroom.  The final
-- absorption inequality cannot be used to manufacture its own critical-scale
-- input.  This theorem makes that anti-circularity condition mechanical.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

headroomRecycledCoefficientProduct :
  (gap B K : ℚ) →
  B * K ≡ gap →
  B * K ≡ gap
headroomRecycledCoefficientProduct gap B K productIsGap = productIsGap

recycledCriticalScaleForcesDataNonpositive :
  (a B K gap : ℚ) →
  B * K ≡ gap →
  a + B * K ≤ gap →
  a ≤ 0ℚ
recycledCriticalScaleForcesDataNonpositive a B K gap productIsGap coefficientHeadroom =
  let
    collapsed : a + gap ≤ gap
    collapsed =
      subst
        (λ selected → a + selected ≤ gap)
        productIsGap
        coefficientHeadroom

    shifted = ℚP.+-monoʳ-≤ (0ℚ - gap) collapsed

    leftMeaning : (a + gap) + (0ℚ - gap) ≡ a
    leftMeaning = solve (a ∷ gap ∷ [])

    rightMeaning : gap + (0ℚ - gap) ≡ 0ℚ
    rightMeaning = solve (gap ∷ [])
  in
  subst
    (λ left → left ≤ 0ℚ)
    leftMeaning
    (subst
      (λ right → (a + gap) + (0ℚ - gap) ≤ right)
      rightMeaning
      shifted)

positiveDataContradictsRecycledCriticalScale :
  (a B K gap : ℚ) →
  0ℚ < a →
  B * K ≡ gap →
  a + B * K ≤ gap →
  0ℚ < 0ℚ
positiveDataContradictsRecycledCriticalScale
    a B K gap aPositive productIsGap coefficientHeadroom =
  ℚP.<-≤-trans
    aPositive
    (recycledCriticalScaleForcesDataNonpositive
      a B K gap productIsGap coefficientHeadroom)

criticalScaleMustBeProvedUpstreamOfFinalHeadroom : Bool
criticalScaleMustBeProvedUpstreamOfFinalHeadroom = true

criticalScaleMustBeProvedUpstreamOfFinalHeadroomIsTrue :
  criticalScaleMustBeProvedUpstreamOfFinalHeadroom ≡ true
criticalScaleMustBeProvedUpstreamOfFinalHeadroomIsTrue = refl
