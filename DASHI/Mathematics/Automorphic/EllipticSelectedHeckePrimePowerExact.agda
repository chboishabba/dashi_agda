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
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
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


------------------------------------------------------------------------
-- ORIGINAL CHECKED-ROW EULER POLYNOMIAL ↔ RECURRENCE CANCELLATION
--
-- Algebra on exact rational coefficients, no infinite Euler-product
-- inversion or unverified analytic convergence.
------------------------------------------------------------------------

primePowerEulerCancellation :
  ∀ a p k →
  primePowerHeckeCoefficient a p (suc (suc k))
    - a * primePowerHeckeCoefficient a p (suc k)
    + p * primePowerHeckeCoefficient a p k
  ≡ 0ℚ
primePowerEulerCancellation a p k =
  solve (a ∷ p ∷
    primePowerHeckeCoefficient a p (suc k) ∷
    primePowerHeckeCoefficient a p k ∷ [])

-- The reciprocal-series identity through the actual p² coefficient:
-- (1-aT+pT²)(1+aT+a_{p²}T²)
--    = 1 - a_{p³}T³ + p*a_{p²}T⁴.
-- It is valid in Q[T] and verified here pointwise for every Q T.
primePowerEulerTruncationTwo :
  ∀ a p T →
  (1ℚ - a * T + p * T * T)
  * (primePowerHeckeCoefficient a p zero
    + primePowerHeckeCoefficient a p (suc zero) * T
    + primePowerHeckeCoefficient a p (suc (suc zero)) * T * T)
  ≡
  1ℚ
    - primePowerHeckeCoefficient a p (suc (suc (suc zero)))
      * T * T * T
    + p * primePowerHeckeCoefficient a p (suc (suc zero))
      * T * T * T * T
primePowerEulerTruncationTwo a p T = solve (a ∷ p ∷ T ∷ [])

-- THE ORIGINAL rowFactorValue from the repository's literal
-- Frobenius fibre count, not a newly chosen polynomial.
rowEulerHeckeTruncationTwo :
  ∀ row T →
  Euler.rowFactorValue row T
    * (rowHeckeCoefficient row zero
      + rowHeckeCoefficient row (suc zero) * T
      + rowHeckeCoefficient row (suc (suc zero)) * T * T)
  ≡ 1ℚ
      - rowHeckeCoefficient row (suc (suc (suc zero)))
        * T * T * T
      + Rows.natToRational (Rows.prime row)
        * rowHeckeCoefficient row (suc (suc zero))
        * T * T * T * T
rowEulerHeckeTruncationTwo row T =
  primePowerEulerTruncationTwo
    (Rows.signedToRational (Rows.frobeniusTrace row))
    (Rows.natToRational (Rows.prime row))
    T

-- Exact cancellation for any exponent at any checked row.
rowHeckeEulerCancellation :
  ∀ row k →
  rowHeckeCoefficient row (suc (suc k))
    - Rows.signedToRational (Rows.frobeniusTrace row)
      * rowHeckeCoefficient row (suc k)
    + Rows.natToRational (Rows.prime row)
      * rowHeckeCoefficient row k
  ≡ 0ℚ
rowHeckeEulerCancellation row k =
  primePowerEulerCancellation
    (Rows.signedToRational (Rows.frobeniusTrace row))
    (Rows.natToRational (Rows.prime row))
    k
