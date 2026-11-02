module DASHI.Analysis.BishopMachinCrossEnvelopeBishopOrderExact where

------------------------------------------------------------------------
-- K04b-DENOM: FIRST POSITIVE-DENOMINATOR / SAME-BISHOP-ORDER WELD.
--
-- Reuse the exact all-Nat cross-multiplied Machin remainder envelope,
-- the source-owned positive-Nat fraction-order theorem, and the
-- vendored Bishop rational embedding/order. No alternative real carrier.
--
-- This result is the canonical NORMALIZED cross-product certificate.
-- The still-open leaf is the literal equality of the two ORIGINAL
-- multi-denominator remainder fractions to this normal form before
-- common-denominator cancellation. Do not confuse them.
--
-- Machin 1706; Bishop/Bridges 1985; Murray 2022 arXiv:2205.08354.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_; _+_)
import Data.Nat.Properties as NatP
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_; _≤_)
open import Data.Integer.Base using (+_)

import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopMachinGeometricEnvelopeNatExact as Cross
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Fractions

normalizedNumerator normalizedDenominator : Nat → Nat
normalizedNumerator n =
  3824 * Cross.pow57121 n + 20 * Cross.pow25 n
normalizedDenominator n =
  suc (2 * n) * (4780 * Cross.pow57121 n)

normalizedNumeratorBelowDenominator : (n : Nat) →
  normalizedNumerator n ≤ normalizedDenominator n
normalizedNumeratorBelowDenominator n =
  Cross.machinGeometricEnvelopeCrossMultiplied n

-- Explicit use of the SAME unnormalised rational backend employed
-- by the Bishop library. Both denominators are the canonical 1.
-- The remaining multi-denominator cancellation is separate.
normalizedRationalOrder : (n : Nat) →
  (+ normalizedNumerator n / 1)
    Q.≤ (+ normalizedDenominator n / 1)
normalizedRationalOrder n =
  Fractions.natFractionLe
    (NatP.*-mono-≤
      (normalizedNumeratorBelowDenominator n)
      NatP.≤-refl)

normalizedBishopOrder : (n : Nat) →
  R._≤_
    (R._⋆ (+ normalizedNumerator n / 1))
    (R._⋆ (+ normalizedDenominator n / 1))
normalizedBishopOrder n =
  RP.p≤q⇒p⋆≤q⋆
    (+ normalizedNumerator n / 1)
    (+ normalizedDenominator n / 1)
    (normalizedRationalOrder n)

------------------------------------------------------------------------
-- K04b-DENOM: ORIGINAL THREE-FACTOR COMMON-DENOMINATOR CERTIFICATE.
--
-- The omitted source magnitudes are
-- 16 / [(2n+1) 5 25^n] + 4 / [(2n+1) 239 57121^n].
-- Their shared integer denominator is exactly
--
-- D_n = (2n+1) * 5 * 239 * 25^n * 57121^n,
--
-- with numerator 16*239*57121^n + 4*5*25^n.
-- The target 4/25^n, after clearing D_n*25^n, becomes
--
--   numerator * 25^n <= 4 * D_n .
--
-- This theorem proves that literal denominator-cleared arithmetic
-- directly from the original all-index Nat cross certificate.
-- Proving the two rational-addition/source-term setoid equalities
-- and positivity of each composite unnormalised denominator is
-- a separate and explicitly tracked final K04b transport leaf.
------------------------------------------------------------------------

sourceCommonDenominator : Nat → Nat
sourceCommonDenominator n =
  (((suc (2 * n) * 5) * 239) * Cross.pow25 n) *
    Cross.pow57121 n

sourceCommonDenominatorFactor :
  (odd p q : Nat) →
  (odd * (4780 * q)) * p ≡
  4 * (((odd * 5) * 239 * p) * q)
sourceCommonDenominatorFactor =
  solve 3
    (λ odd p q →
      ((odd :* (con 4780 :* q)) :* p)
      := (con 4 :*
          ((((odd :* con 5) :* con 239) :* p) :* q)))
    refl

sourceCommonDenominatorCleared : (n : Nat) →
  (normalizedNumerator n * Cross.pow25 n)
  ≤ (4 * sourceCommonDenominator n)
sourceCommonDenominatorCleared n =
  subst
    (λ bound → normalizedNumerator n * Cross.pow25 n ≤ bound)
    (sourceCommonDenominatorFactor
      (suc (2 * n))
      (Cross.pow25 n)
      (Cross.pow57121 n))
    (NatP.*-mono-≤
      (normalizedNumeratorBelowDenominator n)
      NatP.≤-refl)
