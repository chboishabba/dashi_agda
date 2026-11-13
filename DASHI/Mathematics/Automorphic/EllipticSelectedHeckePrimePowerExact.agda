module DASHI.Mathematics.Automorphic.EllipticSelectedHeckePrimePowerExact where

------------------------------------------------------------------------
-- ORIGINAL SELECTED-CURVE FROBENIUS ROW -> HECKE PRIME-POWER RECURRENCE
--
-- All seven prime rows are imported from the original checked
-- EllipticCurveSmallPrimeFrobeniusExact owner, not fabricated.
-- For each GOOD prime row with p and a_p = p+1-#E(F_p):
--
--   a_{p^0} = 1, a_{p^1} = a_p,
--   a_{p^(k+2)} = a_p a_{p^(k+1)} - p a_{p^k}.
--
-- The recurrence algebra is unconditional and source-written on
-- the literal checked finite rows. The theorem does NOT supply
-- an all-prime Frobenius family, Hecke multiplicativity across
-- coprime factors, the modular eigenform, the infinite Euler
-- product, or convergence at s=1. Those remain original K4 gates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 1ℚ; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Mathematics.Arithmetic.EllipticCurveSmallPrimeFrobeniusExact as Rows
import DASHI.Mathematics.Arithmetic.SmallPrimeTruncatedEulerProductExact as Euler

-- Ordinary good-prime recurrence with completely explicit operands.
primePowerHeckeCoefficient : ℚ → ℚ → Nat → ℚ
primePowerHeckeCoefficient a p zero = 1ℚ
primePowerHeckeCoefficient a p (suc zero) = a
primePowerHeckeCoefficient a p (suc (suc k)) =
  a * primePowerHeckeCoefficient a p (suc k)
  - p * primePowerHeckeCoefficient a p k

primePowerConstant : ∀ a p →
  primePowerHeckeCoefficient a p zero ≡ 1ℚ
primePowerConstant a p = refl

primePowerFirst : ∀ a p →
  primePowerHeckeCoefficient a p (suc zero) ≡ a
primePowerFirst a p = refl

primePowerRecurrence : ∀ a p k →
  primePowerHeckeCoefficient a p (suc (suc k))
  ≡ a * primePowerHeckeCoefficient a p (suc k)
    - p * primePowerHeckeCoefficient a p k
primePowerRecurrence a p k = refl

primePowerSecond : ∀ a p →
  primePowerHeckeCoefficient a p (suc (suc zero))
  ≡ a * a - p
primePowerSecond a p = solve (a ∷ p ∷ [])

-- Each row comes from the ORIGINAL F_p fibre-count certificate.
rowHeckeCoefficient : Rows.SmallPrimeFrobeniusRow → Nat → ℚ
rowHeckeCoefficient row =
  primePowerHeckeCoefficient
    (Rows.signedToRational (Rows.frobeniusTrace row))
    (Rows.natToRational (Rows.prime row))

rowHeckeFirstMatchesFrobenius : ∀ row →
  rowHeckeCoefficient row (suc zero)
  ≡ Rows.signedToRational (Rows.frobeniusTrace row)
rowHeckeFirstMatchesFrobenius row = refl

rowHeckeSecondMatchesEulerPolynomial : ∀ row →
  rowHeckeCoefficient row (suc (suc zero))
  ≡
  Rows.signedToRational (Rows.frobeniusTrace row)
    * Rows.signedToRational (Rows.frobeniusTrace row)
  - Rows.natToRational (Rows.prime row)
rowHeckeSecondMatchesEulerPolynomial row =
  primePowerSecond
    (Rows.signedToRational (Rows.frobeniusTrace row))
    (Rows.natToRational (Rows.prime row))

rowHeckeRecurrence : ∀ row k →
  rowHeckeCoefficient row (suc (suc k))
  ≡
  Rows.signedToRational (Rows.frobeniusTrace row)
    * rowHeckeCoefficient row (suc k)
  - Rows.natToRational (Rows.prime row)
    * rowHeckeCoefficient row k
rowHeckeRecurrence row k = refl

-- Selected p=5 is tied directly to its original checked row,
-- not a generic candidate eigenvalue.
p5HeckeFirstIsOriginalFrobenius :
  rowHeckeCoefficient Rows.p5Row (suc zero)
  ≡ Rows.signedToRational (Rows.frobeniusTrace Rows.p5Row)
p5HeckeFirstIsOriginalFrobenius =
  rowHeckeFirstMatchesFrobenius Rows.p5Row

-- Reuse the ORIGINAL seven-prime Euler denominator agreement.
-- This does not turn the finite candidate into a newform.
sevenPrimeEulerAgreement :
  ∀ T →
  Euler.smallPrimeEulerDenominator T
  ≡ Euler.selectedModularEulerDenominator
      Euler.canonicalSelectedModularCandidate T
sevenPrimeEulerAgreement = Euler.canonicalSmallPrimeEulerAgreement
