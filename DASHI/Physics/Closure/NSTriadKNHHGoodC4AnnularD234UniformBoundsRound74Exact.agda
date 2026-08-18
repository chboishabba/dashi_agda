module DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularD234UniformBoundsRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Classical multiplier context: Mikhlin--Hörmander derivative criteria.
-- IMPORTANT: those multiplier theorems do not by themselves prove the
-- pointwise inverse-Fourier |x|^-4 estimate.  That later estimate uses compact
-- support plus four integrations by parts.
--
-- ROUND74 / REMAINING SCALAR C4 DERIVATIVE BOUNDS
--
-- Round68 already proved the exact factorizations
--
-- S''   = 2520 t^3(t-1)^3(2t-1)
-- S'''  = 2520 t^2(t-1)^2(14t^2-14t+3)
-- S'''' =15120 t(t-1)(2t-1)(7t^2-7t+1).
--
-- On 0<=t<=1 this file proves conservative exact absolute bounds
--
-- |S''|   <= 2520,
-- |S'''|  <= 27720,
-- |S''''| <= 90720.
--
-- They are deliberately non-sharp but fully finite.  Together with Round68's
-- sharper |S'|<=315/128 they close boundedness of the scalar transition through
-- derivative order four.  Continuum matrix chain rule and Fourier integration
-- by parts remain separate analytic producers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as Int
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNFiniteGalerkinLocalLipschitzRound28Exact as Abs
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact as C4
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularDerivativeFactorizationRound68Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularD1UniformBoundRound68Exact as D1

one c3 c6 c7 c11 c14 c2520 c27720 c15120 c90720 : ℚ
one = 1ℚ
c3 = Int.+ 3 / 1
c6 = Int.+ 6 / 1
c7 = Int.+ 7 / 1
c11 = Int.+ 11 / 1
c14 = Int.+ 14 / 1
c2520 = Int.+ 2520 / 1
c27720 = Int.+ 27720 / 1
c15120 = Int.+ 15120 / 1
c90720 = Int.+ 90720 / 1

oneNN : 0ℚ ≤ one
oneNN = ℚP.0≤1
c3NN : 0ℚ ≤ c3
c3NN = toWitness {a? = 0ℚ ≤? c3} _
c6NN : 0ℚ ≤ c6
c6NN = toWitness {a? = 0ℚ ≤? c6} _
c7NN : 0ℚ ≤ c7
c7NN = toWitness {a? = 0ℚ ≤? c7} _
c11NN : 0ℚ ≤ c11
c11NN = toWitness {a? = 0ℚ ≤? c11} _
c14NN : 0ℚ ≤ c14
c14NN = toWitness {a? = 0ℚ ≤? c14} _
c2520NN : 0ℚ ≤ c2520
c2520NN = toWitness {a? = 0ℚ ≤? c2520} _
c15120NN : 0ℚ ≤ c15120
c15120NN = toWitness {a? = 0ℚ ≤? c15120} _
minusOneBelowZero : - one ≤ 0ℚ
minusOneBelowZero = toWitness {a? = (- one) ≤? 0ℚ} _
quarterBelowOne : D1.quarter ≤ one
quarterBelowOne = toWitness {a? = D1.quarter ≤? one} _
threeBelowEleven : c3 ≤ c11
threeBelowEleven = toWitness {a? = c3 ≤? c11} _
oneBelowSix : one ≤ c6
oneBelowSix = toWitness {a? = one ≤? c6} _

absBoundFromTwoSided : ∀ {x bound : ℚ} →
  (- bound) ≤ x → x ≤ bound → ∣ x ∣ ≤ bound
absBoundFromTwoSided {x} {bound} lower upper with ℚP.≤-total 0ℚ x
... | inj₁ xNN =
  subst (_≤ bound) (sym (ℚP.0≤p⇒∣p∣≡p xNN)) upper
... | inj₂ xNP =
  let
    negUpperRaw = ℚP.neg-antimono-≤ lower
    negUpper : - x ≤ bound
    negUpper = subst (λ right → - x ≤ right)
      (solve (bound ∷ [])) negUpperRaw
    negXNNRaw = ℚP.neg-antimono-≤ xNP
    negXNN : 0ℚ ≤ - x
    negXNN = subst (λ left → left ≤ - x) (solve []) negXNNRaw
    absNegative : ∣ x ∣ ≡ - x
    absNegative =
      trans
        (sym (ℚP.∣-p∣≡∣p∣ x))
        (ℚP.0≤p⇒∣p∣≡p negXNN)
  in
  subst (_≤ bound) (sym absNegative) negUpper

absTBelowOne : ∀ {t} → D1.UnitInterval t → ∣ t ∣ ≤ one
absTBelowOne {t} interval =
  subst (_≤ one)
    (sym (ℚP.0≤p⇒∣p∣≡p (proj₁ interval)))
    (proj₂ interval)

absTMinusOneBelowOne : ∀ {t} → D1.UnitInterval t → ∣ t - 1ℚ ∣ ≤ one
absTMinusOneBelowOne {t} interval =
  let
    rawLower = ℚP.+-mono-≤ (proj₁ interval) ℚP.≤-refl
    lower : - one ≤ t - 1ℚ
    lower = subst (λ left → left ≤ t - 1ℚ) (solve [])
      (subst (λ right → 0ℚ + (- one) ≤ right) (solve (t ∷ [])) rawLower)
    rawUpper = ℚP.+-mono-≤ (proj₂ interval) minusOneBelowZero
    upper : t - 1ℚ ≤ one
    upper = subst (λ left → left ≤ one) (solve (t ∷ []))
      (subst (λ right → t + (- one) ≤ right) (solve []) rawUpper)
  in
  absBoundFromTwoSided lower upper

absTwoTMinusOneBelowOne : ∀ {t} → D1.UnitInterval t →
  ∣ (t + t) - 1ℚ ∣ ≤ one
absTwoTMinusOneBelowOne {t} interval =
  let
    twoTNN = ℚP.+-mono-≤ (proj₁ interval) (proj₁ interval)
    rawLower = ℚP.+-mono-≤ twoTNN ℚP.≤-refl
    lower : - one ≤ (t + t) - 1ℚ
    lower = subst (λ left → left ≤ (t + t) - 1ℚ) (solve [])
      (subst (λ right → 0ℚ + (- one) ≤ right) (solve (t ∷ [])) rawLower)
    twoTBelowTwo = ℚP.+-mono-≤ (proj₂ interval) (proj₂ interval)
    rawUpper = ℚP.+-mono-≤ twoTBelowTwo ℚP.≤-refl
    upper : (t + t) - 1ℚ ≤ one
    upper = subst (λ left → left ≤ one) (solve (t ∷ []))
      (subst (λ right → (t + t) + (- one) ≤ right) (solve []) rawUpper)
  in
  absBoundFromTwoSided lower upper

unitProduct : ℚ → ℚ
unitProduct t = t * (1ℚ - t)

unitProductNN : ∀ {t} → D1.UnitInterval t → 0ℚ ≤ unitProduct t
unitProductNN = D1.unitProductNonnegative

unitProductBelowOne : ∀ {t} → D1.UnitInterval t → unitProduct t ≤ one
unitProductBelowOne interval =
  ℚP.≤-trans (D1.unitProductBelowQuarter interval) quarterBelowOne

quadratic14Bound : ∀ {t} → D1.UnitInterval t →
  ∣ c14 * C4.square t - c14 * t + c3 ∣ ≤ c11
quadratic14Bound {t} interval =
  let
    u = unitProduct t
    scaledUpper : c14 * u ≤ c14 * one
    scaledUpper =
      let instance cNNI = nonNegative c14NN
      in ℚP.*-monoˡ-≤-nonNeg c14 (unitProductBelowOne interval)
    negLower = ℚP.neg-antimono-≤ scaledUpper
    lowerRaw = ℚP.+-mono-≤ ℚP.≤-refl negLower
    lower : - c11 ≤ c3 - c14 * u
    lower = subst (λ left → left ≤ c3 - c14 * u) (solve [])
      (subst (λ right → c3 + (- (c14 * one)) ≤ right) (solve (u ∷ [])) lowerRaw)
    scaledNN : 0ℚ ≤ c14 * u
    scaledNN =
      let instance
        cNNI = nonNegative c14NN
        uNNI = nonNegative (unitProductNN interval)
        productNNI = ℚP.nonNeg*nonNeg⇒nonNeg c14 u
      in ℚP.nonNegative⁻¹ (c14 * u)
    negUpper = ℚP.neg-antimono-≤ scaledNN
    upperRaw = ℚP.+-mono-≤ ℚP.≤-refl negUpper
    upper3 : c3 - c14 * u ≤ c3
    upper3 = subst (λ left → left ≤ c3) (solve (u ∷ []))
      (subst (λ right → c3 + (- (c14 * u)) ≤ right) (solve []) upperRaw)
    upper = ℚP.≤-trans upper3 threeBelowEleven
  in
  subst (λ x → ∣ x ∣ ≤ c11) (solve (t ∷ []))
    (absBoundFromTwoSided lower upper)

quadratic7Bound : ∀ {t} → D1.UnitInterval t →
  ∣ c7 * C4.square t - c7 * t + 1ℚ ∣ ≤ c6
quadratic7Bound {t} interval =
  let
    u = unitProduct t
    scaledUpper : c7 * u ≤ c7 * one
    scaledUpper =
      let instance cNNI = nonNegative c7NN
      in ℚP.*-monoˡ-≤-nonNeg c7 (unitProductBelowOne interval)
    negLower = ℚP.neg-antimono-≤ scaledUpper
    lowerRaw = ℚP.+-mono-≤ ℚP.≤-refl negLower
    lower : - c6 ≤ one - c7 * u
    lower = subst (λ left → left ≤ one - c7 * u) (solve [])
      (subst (λ right → one + (- (c7 * one)) ≤ right) (solve (u ∷ [])) lowerRaw)
    scaledNN : 0ℚ ≤ c7 * u
    scaledNN =
      let instance
        cNNI = nonNegative c7NN
        uNNI = nonNegative (unitProductNN interval)
        productNNI = ℚP.nonNeg*nonNeg⇒nonNeg c7 u
      in ℚP.nonNegative⁻¹ (c7 * u)
    negUpper = ℚP.neg-antimono-≤ scaledNN
    upperRaw = ℚP.+-mono-≤ ℚP.≤-refl negUpper
    upper1 : one - c7 * u ≤ one
    upper1 = subst (λ left → left ≤ one) (solve (u ∷ []))
      (subst (λ right → one + (- (c7 * u)) ≤ right) (solve []) upperRaw)
    upper = ℚP.≤-trans upper1 oneBelowSix
  in
  subst (λ x → ∣ x ∣ ≤ c6) (solve (t ∷ []))
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

absPositiveConstant : ∀ {c : ℚ} → 0ℚ ≤ c → ∣ c ∣ ≤ c
absPositiveConstant {c} cNN =
  subst (_≤ c) (sym (ℚP.0≤p⇒∣p∣≡p cNN)) ℚP.≤-refl

smoothStep4D2AbsoluteBound : ∀ {t} → D1.UnitInterval t →
  ∣ C4.smoothStep4D2 t ∣ ≤ c2520
smoothStep4D2AbsoluteBound {t} interval =
  let
    b0 = Abs.absoluteProductBound
      (absPositiveConstant c2520NN)
      (absCubeBelowOne (absTBelowOne interval)) c2520NN oneNN
    b1 = Abs.absoluteProductBound b0
      (absCubeBelowOne (absTMinusOneBelowOne interval)) c2520NN oneNN
    b2 = Abs.absoluteProductBound b1
      (absTwoTMinusOneBelowOne interval) c2520NN oneNN
  in
  subst (_≤ c2520)
    (sym (cong ∣_∣ (Factor.smoothStep4D2Factored t))) b2

smoothStep4D3AbsoluteBound : ∀ {t} → D1.UnitInterval t →
  ∣ C4.smoothStep4D3 t ∣ ≤ c27720
smoothStep4D3AbsoluteBound {t} interval =
  let
    b0 = Abs.absoluteProductBound
      (absPositiveConstant c2520NN)
      (absSquareBelowOne (absTBelowOne interval)) c2520NN oneNN
    b1 = Abs.absoluteProductBound b0
      (absSquareBelowOne (absTMinusOneBelowOne interval)) c2520NN oneNN
    b2 = Abs.absoluteProductBound b1
      (quadratic14Bound interval) c2520NN c11NN
  in
  subst (_≤ c27720)
    (sym (cong ∣_∣ (Factor.smoothStep4D3Factored t)))
    (subst (_≤ c27720) (solve []) b2)

smoothStep4D4AbsoluteBound : ∀ {t} → D1.UnitInterval t →
  ∣ C4.smoothStep4D4 t ∣ ≤ c90720
smoothStep4D4AbsoluteBound {t} interval =
  let
    b0 = Abs.absoluteProductBound
      (absPositiveConstant c15120NN)
      (absTBelowOne interval) c15120NN oneNN
    b1 = Abs.absoluteProductBound b0
      (absTMinusOneBelowOne interval) c15120NN oneNN
    b2 = Abs.absoluteProductBound b1
      (absTwoTMinusOneBelowOne interval) c15120NN oneNN
    b3 = Abs.absoluteProductBound b2
      (quadratic7Bound interval) c15120NN c6NN
  in
  subst (_≤ c90720)
    (sym (cong ∣_∣ (Factor.smoothStep4D4Factored t)))
    (subst (_≤ c90720) (solve []) b3)

round74SmoothCutoffD2D3D4UniformBoundsConstructed : Bool
round74SmoothCutoffD2D3D4UniformBoundsConstructed = true

round74ScalarTransitionAllDerivativesThroughFourBounded : Bool
round74ScalarTransitionAllDerivativesThroughFourBounded = true

round74ScalarTransitionAllDerivativesThroughFourBoundedIsTrue :
  round74ScalarTransitionAllDerivativesThroughFourBounded ≡ true
round74ScalarTransitionAllDerivativesThroughFourBoundedIsTrue = refl
