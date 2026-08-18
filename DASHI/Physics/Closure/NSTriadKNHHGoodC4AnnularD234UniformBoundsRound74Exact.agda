module DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularD234UniformBoundsRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Lars Hörmander; Solomon G. Mikhlin.
-- Context: classical multiplier derivative criteria.  The exact finite
-- rational estimates below are repository proofs, not imported multiplier
-- theorems.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND74 / REMAINING SCALAR C4 DERIVATIVE BOUNDS
--
-- Round68 already proved the exact factorizations
--
-- S''   = 2520 t^3(t-1)^3(2t-1)
-- S'''  = 2520 t^2(t-1)^2(14t^2-14t+3)
-- S'''' =15120 t(t-1)(2t-1)(7t^2-7t+1).
--
-- On 0<=t<=1 we prove conservative uniform absolute bounds
--
-- |S''|   <= 2520,
-- |S'''|  <= 7560,
-- |S''''| <= 15120.
--
-- These are intentionally simple exact constants.  They close boundedness of
-- all four scalar transition derivatives together with Round68's sharper
-- |S'|<=315/128.  The continuum matrix chain rule and fourfold Fourier
-- integration by parts remain separate physical/analytic theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as Int
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNFiniteGalerkinLocalLipschitzRound28Exact as Abs
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact as C4
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularDerivativeFactorizationRound68Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularD1UniformBoundRound68Exact as D1

one c3 c7 c14 c2520 c7560 c15120 : ℚ
one = 1ℚ
c3 = Int.+ 3 / 1
c7 = Int.+ 7 / 1
c14 = Int.+ 14 / 1
c2520 = Int.+ 2520 / 1
c7560 = Int.+ 7560 / 1
c15120 = Int.+ 15120 / 1

oneNN : 0ℚ ≤ one
oneNN = ℚP.0≤1
threeNN : 0ℚ ≤ c3
threeNN = ℚP.≤-trans ℚP.0≤1 (subst (1ℚ ≤_) (solve []) ℚP.≤-refl)
c2520NN : 0ℚ ≤ c2520
c2520NN = subst (0ℚ ≤_) (solve []) ℚP.0≤1
c7560NN : 0ℚ ≤ c7560
c7560NN = subst (0ℚ ≤_) (solve []) ℚP.0≤1
c15120NN : 0ℚ ≤ c15120
c15120NN = subst (0ℚ ≤_) (solve []) ℚP.0≤1

absBoundFromTwoSided : ∀ {x bound : ℚ} →
  (- bound) ≤ x → x ≤ bound → ∣ x ∣ ≤ bound
absBoundFromTwoSided {x} {bound} lower upper with ℚP.≤-total 0ℚ x
... | inj₁ xNN =
  subst (_≤ bound) (sym (ℚP.0≤p⇒∣p∣≡p xNN)) upper
... | inj₂ xNP =
  let
    negUpper : - x ≤ bound
    negUpper =
      subst
        (_≤ bound)
        (solve (bound ∷ []))
        (ℚP.neg-antimono-≤ lower)
    absNegative : ∣ x ∣ ≡ - x
    absNegative =
      trans
        (sym (ℚP.∣-p∣≡∣p∣ x))
        (ℚP.0≤p⇒∣p∣≡p (ℚP.neg-antimono-≤ xNP))
  in
  subst (_≤ bound) (sym absNegative) negUpper

absTBelowOne : ∀ {t} → D1.UnitInterval t → ∣ t ∣ ≤ one
absTBelowOne {t} interval =
  subst (_≤ one) (sym (ℚP.0≤p⇒∣p∣≡p (proj₁ interval))) (proj₂ interval)

absTMinusOneBelowOne : ∀ {t} → D1.UnitInterval t → ∣ t - 1ℚ ∣ ≤ one
absTMinusOneBelowOne {t} interval =
  absBoundFromTwoSided
    (subst ((- one) ≤_) (solve (t ∷ [])) (proj₁ interval))
    (subst (_≤ one) (solve (t ∷ [])) (proj₂ interval))

absTwoTMinusOneBelowOne : ∀ {t} → D1.UnitInterval t →
  ∣ (t + t) - 1ℚ ∣ ≤ one
absTwoTMinusOneBelowOne {t} interval =
  absBoundFromTwoSided
    (subst ((- one) ≤_) (solve (t ∷ []))
      (ℚP.+-mono-≤ (proj₁ interval) (proj₁ interval)))
    (subst (_≤ one) (solve (t ∷ []))
      (ℚP.+-mono-≤ (proj₂ interval) (proj₂ interval)))

unitProduct : ℚ → ℚ
unitProduct t = t * (1ℚ - t)

unitProductNN : ∀ {t} → D1.UnitInterval t → 0ℚ ≤ unitProduct t
unitProductNN = D1.unitProductNonnegative

unitProductBelowQuarter : ∀ {t} → D1.UnitInterval t →
  unitProduct t ≤ D1.quarter
unitProductBelowQuarter = D1.unitProductBelowQuarter

quadratic14Bound : ∀ {t} → D1.UnitInterval t →
  ∣ c14 * C4.square t - c14 * t + c3 ∣ ≤ c3
quadratic14Bound {t} interval =
  let
    u = unitProduct t
    uNN = unitProductNN interval
    u≤ = unitProductBelowQuarter interval
    lower : - c3 ≤ c3 - c14 * u
    lower = subst ((- c3) ≤_) (solve (u ∷ [])) u≤
    upper : c3 - c14 * u ≤ c3
    upper = subst (_≤ c3) (solve (u ∷ [])) uNN
  in
  subst (λ x → ∣ x ∣ ≤ c3) (solve (t ∷ []))
    (absBoundFromTwoSided lower upper)

quadratic7Bound : ∀ {t} → D1.UnitInterval t →
  ∣ c7 * C4.square t - c7 * t + 1ℚ ∣ ≤ one
quadratic7Bound {t} interval =
  let
    u = unitProduct t
    uNN = unitProductNN interval
    u≤ = unitProductBelowQuarter interval
    lower : - one ≤ one - c7 * u
    lower = subst ((- one) ≤_) (solve (u ∷ [])) u≤
    upper : one - c7 * u ≤ one
    upper = subst (_≤ one) (solve (u ∷ [])) uNN
  in
  subst (λ x → ∣ x ∣ ≤ one) (solve (t ∷ []))
    (absBoundFromTwoSided lower upper)

absSquareBelowOne : ∀ {x} → ∣ x ∣ ≤ one → ∣ C4.square x ∣ ≤ one
absSquareBelowOne {x} x≤ =
  subst (_≤ one)
    (sym (ℚP.∣p*q∣≡∣p∣*∣q∣ x x))
    (Abs.absoluteProductBound x≤ x≤ oneNN oneNN)

absCubeBelowOne : ∀ {x} → ∣ x ∣ ≤ one → ∣ C4.cube x ∣ ≤ one
absCubeBelowOne {x} x≤ =
  let sq≤ = absSquareBelowOne x≤ in
  subst (_≤ one)
    (sym (ℚP.∣p*q∣≡∣p∣*∣q∣ (C4.square x) x))
    (Abs.absoluteProductBound sq≤ x≤ oneNN oneNN)

smoothStep4D2AbsoluteBound : ∀ {t} → D1.UnitInterval t →
  ∣ C4.smoothStep4D2 t ∣ ≤ c2520
smoothStep4D2AbsoluteBound {t} interval =
  let
    t3≤ = absCubeBelowOne (absTBelowOne interval)
    m3≤ = absCubeBelowOne (absTMinusOneBelowOne interval)
    lin≤ = absTwoTMinusOneBelowOne interval
    first = Abs.absoluteProductBound t3≤ m3≤ oneNN oneNN
    second = Abs.absoluteProductBound first lin≤ oneNN oneNN
    scaled = Abs.absoluteProductBound
      (subst (_≤ c2520) (ℚP.0≤p⇒∣p∣≡p c2520NN) ℚP.≤-refl)
      second c2520NN oneNN
  in
  subst (_≤ c2520)
    (sym (cong ∣_∣ (Factor.smoothStep4D2Factored t)))
    (subst (_≤ c2520) (solve []) scaled)
  where
  open import Relation.Binary.PropositionalEquality using (cong)

smoothStep4D3AbsoluteBound : ∀ {t} → D1.UnitInterval t →
  ∣ C4.smoothStep4D3 t ∣ ≤ c7560
smoothStep4D3AbsoluteBound {t} interval =
  let
    t2≤ = absSquareBelowOne (absTBelowOne interval)
    m2≤ = absSquareBelowOne (absTMinusOneBelowOne interval)
    q≤ = quadratic14Bound interval
    first = Abs.absoluteProductBound t2≤ m2≤ oneNN oneNN
    second = Abs.absoluteProductBound first q≤ oneNN threeNN
    cAbs : ∣ c2520 ∣ ≤ c2520
    cAbs = subst (_≤ c2520) (ℚP.0≤p⇒∣p∣≡p c2520NN) ℚP.≤-refl
    scaled = Abs.absoluteProductBound cAbs second c2520NN threeNN
  in
  subst (_≤ c7560)
    (sym (cong ∣_∣ (Factor.smoothStep4D3Factored t)))
    (subst (_≤ c7560) (solve []) scaled)
  where
  open import Relation.Binary.PropositionalEquality using (cong)

smoothStep4D4AbsoluteBound : ∀ {t} → D1.UnitInterval t →
  ∣ C4.smoothStep4D4 t ∣ ≤ c15120
smoothStep4D4AbsoluteBound {t} interval =
  let
    t≤ = absTBelowOne interval
    m≤ = absTMinusOneBelowOne interval
    lin≤ = absTwoTMinusOneBelowOne interval
    q≤ = quadratic7Bound interval
    first = Abs.absoluteProductBound t≤ m≤ oneNN oneNN
    second = Abs.absoluteProductBound first lin≤ oneNN oneNN
    third = Abs.absoluteProductBound second q≤ oneNN oneNN
    cAbs : ∣ c15120 ∣ ≤ c15120
    cAbs = subst (_≤ c15120) (ℚP.0≤p⇒∣p∣≡p c15120NN) ℚP.≤-refl
    scaled = Abs.absoluteProductBound cAbs third c15120NN oneNN
  in
  subst (_≤ c15120)
    (sym (cong ∣_∣ (Factor.smoothStep4D4Factored t)))
    scaled
  where
  open import Relation.Binary.PropositionalEquality using (cong)

round74SmoothCutoffD2D3D4UniformBoundsConstructed : Bool
round74SmoothCutoffD2D3D4UniformBoundsConstructed = true

round74ScalarTransitionAllDerivativesThroughFourBounded : Bool
round74ScalarTransitionAllDerivativesThroughFourBounded = true

round74ScalarTransitionAllDerivativesThroughFourBoundedIsTrue :
  round74ScalarTransitionAllDerivativesThroughFourBounded ≡ true
round74ScalarTransitionAllDerivativesThroughFourBoundedIsTrue = refl
