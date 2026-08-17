module DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularAmplitudeBoundRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 68 / EXACT CUTOFF AMPLITUDE BOUND
--
-- The fourth-order smoothstep admits the positive Bernstein expansion
--
--   S(t) = 126 t^5 u^4 + 84 t^6 u^3 + 36 t^7 u^2 + 9 t^8 u + t^9,
--   u = 1-t.
--
-- The complementary first five binomial terms are also nonnegative, and the
-- complete nine-degree binomial sum is exactly
--
--   (t+u)^9 = 1.
--
-- Therefore on 0<=t<=1,
--
--   0 <= S(t) <= 1.
--
-- This avoids importing monotonicity from calculus and supplies the literal
-- cutoff contraction needed in the localized multiplier estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact as C4
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularD1UniformBoundRound68Exact as D1

c9 c36 c84 c126 : ℚ
c9 = Int.+ 9 / 1
c36 = Int.+ 36 / 1
c84 = Int.+ 84 / 1
c126 = Int.+ 126 / 1

pow : ℚ → Nat → ℚ
pow x zero = 1ℚ
pow x (suc n) = x * pow x n

powNonnegative : ∀ x n → 0ℚ ≤ x → 0ℚ ≤ pow x n
powNonnegative x zero xNN = ℚP.0≤1
powNonnegative x (suc n) xNN =
  let
    tailNN = powNonnegative x n xNN
    instance
      xNNI = nonNegative xNN
      tailNNI = nonNegative tailNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg x (pow x n)
  in
  ℚP.nonNegative⁻¹ (pow x (suc n))

mulNonnegative : ∀ {a b} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
mulNonnegative {a} {b} aNN bNN =
  let instance
    aNNI = nonNegative aNN
    bNNI = nonNegative bNN
    productNNI = ℚP.nonNeg*nonNeg⇒nonNeg a b
  in ℚP.nonNegative⁻¹ (a * b)

addNonnegative : ∀ {a b} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
addNonnegative {a} {b} aNN bNN =
  subst
    (λ lower → lower ≤ a + b)
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤ aNN bNN)

oneMinus : ℚ → ℚ
oneMinus t = 1ℚ - t

bernsteinUpper : ℚ → ℚ
bernsteinUpper t =
    c126 * pow t 5 * pow (oneMinus t) 4
  + c84 * pow t 6 * pow (oneMinus t) 3
  + c36 * pow t 7 * pow (oneMinus t) 2
  + c9 * pow t 8 * oneMinus t
  + pow t 9

bernsteinLowerComplement : ℚ → ℚ
bernsteinLowerComplement t =
    pow (oneMinus t) 9
  + c9 * t * pow (oneMinus t) 8
  + c36 * pow t 2 * pow (oneMinus t) 7
  + c84 * pow t 3 * pow (oneMinus t) 6
  + c126 * pow t 4 * pow (oneMinus t) 5

smoothStepBernsteinExact : ∀ t → C4.smoothStep4 t ≡ bernsteinUpper t
smoothStepBernsteinExact t = solve (t ∷ [])

fullBernsteinPartitionExact : ∀ t →
  bernsteinLowerComplement t + bernsteinUpper t ≡ 1ℚ
fullBernsteinPartitionExact t = solve (t ∷ [])

coefficient9Nonnegative : 0ℚ ≤ c9
coefficient9Nonnegative = toWitness {a? = 0ℚ ≤? c9} _

coefficient36Nonnegative : 0ℚ ≤ c36
coefficient36Nonnegative = toWitness {a? = 0ℚ ≤? c36} _

coefficient84Nonnegative : 0ℚ ≤ c84
coefficient84Nonnegative = toWitness {a? = 0ℚ ≤? c84} _

coefficient126Nonnegative : 0ℚ ≤ c126
coefficient126Nonnegative = toWitness {a? = 0ℚ ≤? c126} _

bernsteinMonomialNonnegative :
  ∀ coefficient t m n →
  0ℚ ≤ coefficient → 0ℚ ≤ t → 0ℚ ≤ oneMinus t →
  0ℚ ≤ coefficient * pow t m * pow (oneMinus t) n
bernsteinMonomialNonnegative coefficient t m n cNN tNN uNN =
  mulNonnegative
    (mulNonnegative cNN (powNonnegative t m tNN))
    (powNonnegative (oneMinus t) n uNN)

bernsteinUpperNonnegative : ∀ {t} → D1.UnitInterval t →
  0ℚ ≤ bernsteinUpper t
bernsteinUpperNonnegative {t} interval =
  let
    tNN = proj₁ interval
    uNN = D1.oneMinusNonnegative (proj₂ interval)
    a = bernsteinMonomialNonnegative c126 t 5 4 coefficient126Nonnegative tNN uNN
    b = bernsteinMonomialNonnegative c84 t 6 3 coefficient84Nonnegative tNN uNN
    c = bernsteinMonomialNonnegative c36 t 7 2 coefficient36Nonnegative tNN uNN
    d : 0ℚ ≤ c9 * pow t 8 * oneMinus t
    d = mulNonnegative
      (mulNonnegative coefficient9Nonnegative (powNonnegative t 8 tNN)) uNN
    e = powNonnegative t 9 tNN
  in
  addNonnegative a (addNonnegative b (addNonnegative c (addNonnegative d e)))

bernsteinLowerComplementNonnegative : ∀ {t} → D1.UnitInterval t →
  0ℚ ≤ bernsteinLowerComplement t
bernsteinLowerComplementNonnegative {t} interval =
  let
    tNN = proj₁ interval
    uNN = D1.oneMinusNonnegative (proj₂ interval)
    a = powNonnegative (oneMinus t) 9 uNN
    b : 0ℚ ≤ c9 * t * pow (oneMinus t) 8
    b = mulNonnegative
      (mulNonnegative coefficient9Nonnegative tNN)
      (powNonnegative (oneMinus t) 8 uNN)
    c = bernsteinMonomialNonnegative c36 t 2 7 coefficient36Nonnegative tNN uNN
    d = bernsteinMonomialNonnegative c84 t 3 6 coefficient84Nonnegative tNN uNN
    e = bernsteinMonomialNonnegative c126 t 4 5 coefficient126Nonnegative tNN uNN
  in
  addNonnegative a (addNonnegative b (addNonnegative c (addNonnegative d e)))

smoothStep4Nonnegative : ∀ {t} → D1.UnitInterval t →
  0ℚ ≤ C4.smoothStep4 t
smoothStep4Nonnegative {t} interval =
  subst (0ℚ ≤_) (sym (smoothStepBernsteinExact t))
    (bernsteinUpperNonnegative interval)

smoothStep4BelowOne : ∀ {t} → D1.UnitInterval t →
  C4.smoothStep4 t ≤ 1ℚ
smoothStep4BelowOne {t} interval =
  let
    lowerNN = bernsteinLowerComplementNonnegative interval
    addLower : 0ℚ + bernsteinUpper t
      ≤ bernsteinLowerComplement t + bernsteinUpper t
    addLower = ℚP.+-monoʳ-≤ (bernsteinUpper t) lowerNN
    upper≤one : bernsteinUpper t ≤ 1ℚ
    upper≤one =
      subst (λ left → left ≤ 1ℚ) (ℚP.+-identityˡ (bernsteinUpper t))
        (subst (λ right → 0ℚ + bernsteinUpper t ≤ right)
          (fullBernsteinPartitionExact t) addLower)
  in
  subst (λ left → left ≤ 1ℚ) (sym (smoothStepBernsteinExact t)) upper≤one

round68SmoothCutoffAmplitudeInUnitInterval : Bool
round68SmoothCutoffAmplitudeInUnitInterval = true

round68SmoothCutoffAmplitudeInUnitIntervalIsTrue :
  round68SmoothCutoffAmplitudeInUnitInterval ≡ true
round68SmoothCutoffAmplitudeInUnitIntervalIsTrue = refl
