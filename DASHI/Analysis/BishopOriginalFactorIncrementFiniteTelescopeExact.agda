module DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP REAL: FINITE ENDPOINT INTEGRATION BY TELESCOPING.
--
-- Reuses the actual division-free BishopFactorDerivativeAt receipt.
-- For any finite discrete walk x_(n+1) = x_n + h_n, choose the
-- original factor quotient q_n of f at x_n. Then, exactly,
--
--   f(x_N)-f(x_0) ~= sum_(n<N) h_n*q_n.
--
-- This result is finite, constructive, works in the pinned Bishop
-- real setoid, and requires neither MVT nor an abstract FTC record.
-- It is NOT the terminal LOG theorem: passing from finite mesh
-- quadratures to continuous endpoint bounds requires a certified
-- mesh-uniform quotient modulus. No such modulus is assumed here.
--
-- Attribution: Bishop/Bridges, Murray/Csimma pinned real and sequence;
-- DASHI BishopFactorDerivativeExact division-free calculus.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopFactorDerivativeExact as Factor

-- Source-native finite walk: no equality comparison or division by
-- the number of cells is used to select the interval vertices.
finiteWalk : R.ℝ → (Nat → R.ℝ) → Nat → R.ℝ
finiteWalk start steps zero = start
finiteWalk start steps (suc n) =
  R._+_ (finiteWalk start steps n) (steps n)

-- Local actual increment, of the same function/carrier at each stage.
finiteIncrement :
  (f : R.ℝ → R.ℝ) →
  (start : R.ℝ) →
  (steps : Nat → R.ℝ) →
  Nat → R.ℝ
finiteIncrement f start steps n =
  R._-_
    (f (finiteWalk start steps (suc n)))
    (f (finiteWalk start steps n))

-- A finite sum defined with identical natural recursion to the
-- original Seq.SeriesOf, but with source-visible zero and successor
-- equations suitable for a direct ring proof.
sumFinite : (Nat → R.ℝ) → Nat → R.ℝ
sumFinite terms zero = R.0ℝ
sumFinite terms (suc n) =
  R._+_ (sumFinite terms n) (terms n)

-- Constructive endpoint FTC for discrete increments on pinned
-- Bishop reals. No differentiability or continuity assumptions.
finiteIncrementTelescopes :
  (f : R.ℝ → R.ℝ) →
  (start : R.ℝ) →
  (steps : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (sumFinite (finiteIncrement f start steps) n)
    (R._-_
      (f (finiteWalk start steps n))
      (f start))
finiteIncrementTelescopes f start steps zero =
  let open RP.ℝ-Solver in
  solve 1
    (λ initial → Κ 0ℚᵘ ⊜ initial ⊖ initial)
    RP.≃-refl
    (f start)
finiteIncrementTelescopes f start steps (suc n) =
  RP.≃-trans
    (RP.+-cong
      (finiteIncrementTelescopes f start steps n)
      RP.≃-refl)
    (let open RP.ℝ-Solver in
     solve 3
       (λ old first next →
         (old ⊖ first) ⊕ (next ⊖ old)
         ⊜ next ⊖ first)
       RP.≃-refl
       (f (finiteWalk start steps n))
       (f start)
       (f (finiteWalk start steps (suc n))))

-- The exact source quotient at each walk vertex, not a chosen
-- derivative approximation or a separately defined difference.
finiteFactorQuotient :
  (f : R.ℝ → R.ℝ) →
  (start : R.ℝ) →
  (steps : Nat → R.ℝ) →
  (derivative : Nat → R.ℝ) →
  ((n : Nat) →
    Factor.BishopFactorDerivativeAt
      f (finiteWalk start steps n)
      (derivative n)) →
  Nat → R.ℝ
finiteFactorQuotient f start steps derivative receipts n =
  Factor.quotient (receipts n) (steps n)

-- A source-constructed finite increment-to-endpoint identity:
-- the derivative receipt itself supplies every factorization;
-- summing those factorizations consumes no analytic axiom.

finiteIncrementIsFactor :
  (f : R.ℝ → R.ℝ) →
  (start : R.ℝ) →
  (steps derivative : Nat → R.ℝ) →
  (receipts : (n : Nat) →
    Factor.BishopFactorDerivativeAt
      f (finiteWalk start steps n)
      (derivative n)) →
  (n : Nat) →
  R._≃_
    (finiteIncrement f start steps n)
    (R._*_ (steps n)
      (finiteFactorQuotient f start steps derivative receipts n))
finiteIncrementIsFactor f start steps derivative receipts n =
  Factor.incrementFactorisation (receipts n) (steps n)

finiteFactorSumIsIncrementSum :
  (f : R.ℝ → R.ℝ) →
  (start : R.ℝ) →
  (steps derivative : Nat → R.ℝ) →
  (receipts : (n : Nat) →
    Factor.BishopFactorDerivativeAt
      f (finiteWalk start steps n)
      (derivative n)) →
  (n : Nat) →
  R._≃_
    (sumFinite (finiteIncrement f start steps) n)
    (sumFinite
      (λ j → R._*_ (steps j)
        (finiteFactorQuotient f start steps derivative receipts j))
      n)
finiteFactorSumIsIncrementSum f start steps derivative receipts zero =
  RP.≃-refl
finiteFactorSumIsIncrementSum f start steps derivative receipts (suc n) =
  RP.+-cong
    (finiteFactorSumIsIncrementSum f start steps derivative receipts n)
    (finiteIncrementIsFactor f start steps derivative receipts n)

originalBishopFactorFiniteEndpointFTC :
  (f : R.ℝ → R.ℝ) →
  (start : R.ℝ) →
  (steps derivative : Nat → R.ℝ) →
  (receipts : (n : Nat) →
    Factor.BishopFactorDerivativeAt
      f (finiteWalk start steps n)
      (derivative n)) →
  (n : Nat) →
  R._≃_
    (R._-_
      (f (finiteWalk start steps n))
      (f start))
    (sumFinite
      (λ j → R._*_ (steps j)
        (finiteFactorQuotient f start steps derivative receipts j))
      n)
originalBishopFactorFiniteEndpointFTC f start steps derivative receipts n =
  RP.≃-trans
    (RP.≃-symm
      (finiteIncrementTelescopes f start steps n))
    (finiteFactorSumIsIncrementSum
      f start steps derivative receipts n)

------------------------------------------------------------------------
-- QUANTITATIVE FINITE INTEGRATION: TRIANGLE MAJORANT.
--
-- The exact endpoint telescope plus the Bishop triangle inequality
-- gives a finite error budget. This is the proof-bearing recipient
-- for a future mesh-uniform source quotient modulus.
------------------------------------------------------------------------

sumFiniteAbsoluteTriangle :
  (terms : Nat → R.ℝ) →
  (n : Nat) →
  R._≤_
    (R.∣ sumFinite terms n ∣)
    (sumFinite (λ j → R.∣ terms j ∣) n)
sumFiniteAbsoluteTriangle terms zero =
  RP.≤-reflexive (RP.nonNegx⇒∣x∣≃x RP.nonNeg0)
sumFiniteAbsoluteTriangle terms (suc n) =
  RP.≤-trans
    (RP.∣x+y∣≤∣x∣+∣y∣
      (sumFinite terms n)
      (terms n))
    (RP.+-mono-≤
      (sumFiniteAbsoluteTriangle terms n)
      RP.≤-refl)

-- Direct original Bishop endpoint inequality, with NO real/complex
-- carrier transport or assumption that derivative values can replace
-- factor quotients at a positive step.
originalBishopFiniteEndpointAbsoluteBound :
  (f : R.ℝ → R.ℝ) →
  (start : R.ℝ) →
  (steps derivative : Nat → R.ℝ) →
  (receipts : (n : Nat) →
    Factor.BishopFactorDerivativeAt
      f (finiteWalk start steps n)
      (derivative n)) →
  (cells : Nat) →
  R._≤_
    (R.∣ R._-_
      (f (finiteWalk start steps cells))
      (f start) ∣)
    (sumFinite
      (λ j → R.∣ R._*_ (steps j)
        (finiteFactorQuotient f start steps derivative receipts j) ∣)
      cells)
originalBishopFiniteEndpointAbsoluteBound
    f start steps derivative receipts cells =
  RP.≤-respˡ-≃
    (RP.∣-∣-cong
      (originalBishopFactorFiniteEndpointFTC
        f start steps derivative receipts cells))
    (sumFiniteAbsoluteTriangle
      (λ j → R._*_ (steps j)
        (finiteFactorQuotient f start steps derivative receipts j))
      cells)
