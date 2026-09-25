{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityEuclideanLorentzianF2FirewallExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- EUCLIDEAN F^2 POSITIVITY != LORENTZIAN F_{mu nu}F^{mu nu} POSITIVITY
--
-- For nonnegative electric/magnetic square coordinates E2,B2:
--
--   Euclidean curvature norm:  E2 + B2
--   Lorentzian invariant:      2 (B2 - E2)
--
-- The first is positive for every nonzero field.  The second has indefinite
-- sign.  Therefore the strict positive Euclidean Wilson/Haar F^2 numerator
-- cannot be inserted into the Lorentzian trace anomaly without an explicit
-- Wick/continuation same-object theorem.
------------------------------------------------------------------------

euclideanF2 : ℚ → ℚ → ℚ
euclideanF2 electricSquare magneticSquare =
  electricSquare + magneticSquare

lorentzianF2 : ℚ → ℚ → ℚ
lorentzianF2 electricSquare magneticSquare =
  (1ℚ + 1ℚ) * (magneticSquare - electricSquare)

electricDominatedEuclideanValue :
  euclideanF2 1ℚ 0ℚ ≡ 1ℚ
electricDominatedEuclideanValue =
  ℚRing.solve []

electricDominatedLorentzianValue :
  lorentzianF2 1ℚ 0ℚ ≡ - (1ℚ + 1ℚ)
electricDominatedLorentzianValue =
  ℚRing.solve []

electricDominatedEuclideanPositive :
  0ℚ < euclideanF2 1ℚ 0ℚ
electricDominatedEuclideanPositive =
  subst
    (λ value → 0ℚ < value)
    (sym electricDominatedEuclideanValue)
    (ℚP.positive⁻¹ 1ℚ)

twoPositive : 0ℚ < (1ℚ + 1ℚ)
twoPositive =
  ℚP.+-mono-<-<
    (ℚP.positive⁻¹ 1ℚ)
    (ℚP.positive⁻¹ 1ℚ)

electricDominatedLorentzianNegative :
  lorentzianF2 1ℚ 0ℚ < 0ℚ
electricDominatedLorentzianNegative =
  subst
    (λ value → value < 0ℚ)
    (sym electricDominatedLorentzianValue)
    (ℚP.neg-mono-< twoPositive)

euclideanF2PositivityImpliesLorentzianF2Positivity : Bool
euclideanF2PositivityImpliesLorentzianF2Positivity = false

euclideanF2PositivityImpliesLorentzianF2PositivityIsFalse :
  euclideanF2PositivityImpliesLorentzianF2Positivity ≡ false
euclideanF2PositivityImpliesLorentzianF2PositivityIsFalse = refl

wickContinuationSameObjectTheoremRequired : Bool
wickContinuationSameObjectTheoremRequired = Agda.Builtin.Bool.true
