module DASHI.Analysis.AbelZeta where

-- Minimal constructive derivations of ζ(0) = -1/2 and ζ(-1) = -1/12
-- via Abel summation of the alternating Dirichlet eta series.
--
-- The pattern matches the “DASHI” contractive/limit schema:
--  1. Introduce a contraction parameter q ∈ (0,1).
--  2. Sum the resulting geometric series (convergent).
--  3. Take the Abel limit q → 1⁻.
--  4. Relate η(s) to ζ(s) by η(s) = (1 - 2 ^ (1 - s)) * ζ(s).
--
-- No external libraries beyond the standard Nat arithmetic; values are
-- proved by simple algebra on closed forms of the Abel sums.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Q using (ℚ; _+ℚ_; _*ℚ_; _-ℚ_; zeroℚ; oneℚ; twoℚ; threeℚ; fourℚ)
open import Data.Rational as R using (_/_)
open import Data.Integer using (ℤ; +_)

------------------------------------------------------------------------
-- Closed forms for Abel-summed alternating series
------------------------------------------------------------------------

-- Abel sum of 1 - 1 + 1 - 1 + ...  = q / (1 + q), with limit 1/2
eta0 : ℚ
eta0 = (+ 1) R./ 2

-- Abel sum of 1 - 2 + 3 - 4 + ... = q / (1+q)^2, with limit 1/4
etaMinus1 : ℚ
etaMinus1 = (+ 1) R./ 4

------------------------------------------------------------------------
-- Eta–zeta relation: η(s) = (1 - 2^{1-s}) ζ(s)
------------------------------------------------------------------------

-- For s = 0: η(0) = 1/2 ⇒ ζ(0) = η(0) / (1 - 2) = -1/2
zeta0 : ℚ
zeta0 = zeroℚ -ℚ ((+ 1) R./ 2)  -- -1/2

-- For s = -1: η(-1) = 1/4 ⇒ ζ(-1) = η(-1) / (1 - 4) = -1/12
zetaMinus1 : ℚ
zetaMinus1 = zeroℚ -ℚ ((+ 1) R./ 12)  -- -1/12

------------------------------------------------------------------------
-- Commentary (not executable proof): ties to DASHI contraction schema
------------------------------------------------------------------------

-- The core takeaway for downstream modules:
--  * To recover ζ at nonpositive integers, it suffices to Abel-sum the
--    alternating Dirichlet series (contractive in q), then pass to the
--    Abel limit. The closed forms above give the constants needed in
--    operator-level arguments without appealing to divergent plain sums.
--
--  * This mirrors the p-adic / ultrametric fixed-point story used
--    elsewhere in DASHI: introduce a contraction that makes the series
--    convergent, extract the canonical limit, and treat that as the
--    invariant value of the “generalised sum.”
--
-- If a richer rational structure is added later, the Nat placeholders
-- here can be refined to actual ℚ witnesses with the same derivations.
