module DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularD1UniformBoundRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 68 / EXPLICIT QUANTITATIVE CUTOFF BOUND
--
-- The factored derivative from the companion file is
--
--   S'(t) = 630 [t(1-t)]^4.
--
-- On 0<=t<=1, complete the square exactly:
--
--   t(1-t) + (t-1/2)^2 = 1/4.
--
-- Hence 0 <= t(1-t) <= 1/4 and therefore
--
--   0 <= S'(t) <= 630/4^4 = 315/128.
--
-- This is the first literal universal derivative constant for the smooth
-- annular transition.  It is deliberately rigorous rather than sharp-by-
-- numerics, and it feeds the first-order commutator multiplier bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact as C4
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularDerivativeFactorizationRound68Exact as Factor

half quarter d1Bound c630 : ℚ
half = Int.+ 1 / 2
quarter = Int.+ 1 / 4
d1Bound = Int.+ 315 / 128
c630 = Int.+ 630 / 1

quarterNonnegative : 0ℚ ≤ quarter
quarterNonnegative = toWitness {a? = 0ℚ ≤? quarter} _

c630Nonnegative : 0ℚ ≤ c630
c630Nonnegative = toWitness {a? = 0ℚ ≤? c630} _

UnitInterval : ℚ → Set
UnitInterval t = (0ℚ ≤ t) × (t ≤ 1ℚ)

oneMinusNonnegative : ∀ {t} → t ≤ 1ℚ → 0ℚ ≤ 1ℚ - t
oneMinusNonnegative {t} t≤1 =
  let
    negated : - 1ℚ ≤ - t
    negated = ℚP.neg-antimono-≤ t≤1
    shifted : 1ℚ + (- 1ℚ) ≤ 1ℚ + (- t)
    shifted = ℚP.+-monoˡ-≤ 1ℚ negated
  in
  subst (λ left → left ≤ 1ℚ - t) (solve [])
    (subst (λ right → 1ℚ + (- 1ℚ) ≤ right) (solve (t ∷ [])) shifted)

unitProduct : ℚ → ℚ
unitProduct t = t * (1ℚ - t)

unitProductNonnegative : ∀ {t} → UnitInterval t → 0ℚ ≤ unitProduct t
unitProductNonnegative {t} interval =
  let
    tNN = proj₁ interval
    omtNN = oneMinusNonnegative (proj₂ interval)
    instance
      tNNI = nonNegative tNN
      omtNNI = nonNegative omtNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg t (1ℚ - t)
  in
  ℚP.nonNegative⁻¹ (unitProduct t)

completionSquare : ∀ t →
  unitProduct t + L2.square (t - half) ≡ quarter
completionSquare t = solve (t ∷ [])

unitProductBelowQuarter : ∀ {t} → UnitInterval t → unitProduct t ≤ quarter
unitProductBelowQuarter {t} interval =
  let
    squareNN = L2.squareNonnegative (t - half)
    addSquare : unitProduct t + 0ℚ ≤ unitProduct t + L2.square (t - half)
    addSquare = ℚP.+-monoˡ-≤ (unitProduct t) squareNN
  in
  subst (λ left → left ≤ quarter) (ℚP.+-identityʳ (unitProduct t))
    (subst (λ right → unitProduct t + 0ℚ ≤ right)
      (completionSquare t) addSquare)

unitProductSquareBelowQuarterSquare : ∀ {t} → UnitInterval t →
  L2.square (unitProduct t) ≤ L2.square quarter
unitProductSquareBelowQuarterSquare {t} interval =
  L2.nonnegativeProductMonotone
    (unitProductNonnegative interval)
    (unitProductNonnegative interval)
    quarterNonnegative quarterNonnegative
    (unitProductBelowQuarter interval)
    (unitProductBelowQuarter interval)

unitProductFourthBelowQuarterFourth : ∀ {t} → UnitInterval t →
  C4.fourth (unitProduct t) ≤ C4.fourth quarter
unitProductFourthBelowQuarterFourth {t} interval =
  let
    squareNN = L2.squareNonnegative (unitProduct t)
    quarterSquareNN = L2.squareNonnegative quarter
    square≤ = unitProductSquareBelowQuarterSquare interval
  in
  L2.nonnegativeProductMonotone
    squareNN squareNN quarterSquareNN quarterSquareNN square≤ square≤

smoothStep4D1Nonnegative : ∀ {t} → UnitInterval t →
  0ℚ ≤ C4.smoothStep4D1 t
smoothStep4D1Nonnegative {t} interval =
  let
    uNN = unitProductNonnegative interval
    u2NN = L2.squareNonnegative (unitProduct t)
    u4NN : 0ℚ ≤ C4.fourth (unitProduct t)
    u4NN =
      let instance
        leftNNI = nonNegative u2NN
        rightNNI = nonNegative u2NN
        productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
          (L2.square (unitProduct t)) (L2.square (unitProduct t))
      in ℚP.nonNegative⁻¹ (C4.fourth (unitProduct t))
    productNN : 0ℚ ≤ c630 * C4.fourth (unitProduct t)
    productNN =
      let instance
        cNNI = nonNegative c630Nonnegative
        uNNI = nonNegative u4NN
        productNNI = ℚP.nonNeg*nonNeg⇒nonNeg c630 (C4.fourth (unitProduct t))
      in ℚP.nonNegative⁻¹ (c630 * C4.fourth (unitProduct t))
    factorMeaning :
      C4.smoothStep4D1 t ≡ c630 * C4.fourth (unitProduct t)
    factorMeaning = trans
      (Factor.smoothStep4D1Factored t)
      (solve (t ∷ []))
  in
  subst (0ℚ ≤_) (sym factorMeaning) productNN

smoothStep4D1UniformBound : ∀ {t} → UnitInterval t →
  C4.smoothStep4D1 t ≤ d1Bound
smoothStep4D1UniformBound {t} interval =
  let
    fourth≤ = unitProductFourthBelowQuarterFourth interval
    scaled : c630 * C4.fourth (unitProduct t)
      ≤ c630 * C4.fourth quarter
    scaled =
      let instance cNNI = nonNegative c630Nonnegative
      in ℚP.*-monoˡ-≤-nonNeg c630 fourth≤
    leftMeaning :
      C4.smoothStep4D1 t ≡ c630 * C4.fourth (unitProduct t)
    leftMeaning = trans
      (Factor.smoothStep4D1Factored t)
      (solve (t ∷ []))
    rightMeaning : c630 * C4.fourth quarter ≡ d1Bound
    rightMeaning = solve []
  in
  subst (λ left → left ≤ d1Bound) (sym leftMeaning)
    (subst (λ right → c630 * C4.fourth (unitProduct t) ≤ right)
      rightMeaning scaled)

round68SmoothCutoffD1Bound315Over128 : Bool
round68SmoothCutoffD1Bound315Over128 = true

round68SmoothCutoffD1Bound315Over128IsTrue :
  round68SmoothCutoffD1Bound315Over128 ≡ true
round68SmoothCutoffD1Bound315Over128IsTrue = refl
