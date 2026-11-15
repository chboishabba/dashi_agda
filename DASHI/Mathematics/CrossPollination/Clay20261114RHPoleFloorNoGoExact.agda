{-# OPTIONS --safe #-}
module DASHI.Mathematics.CrossPollination.Clay20261114RHPoleFloorNoGoExact where

------------------------------------------------------------------------
-- SOURCE-CORRECT RH ATTACHMENT NEGATIVE CONTROL (14 NOVEMBER 2026)
--
-- The attachment asserts that the negative local contribution from
-- a zero to the horizontal second derivative of log|xi| obeys
--     -1 / (sigma - beta)^2 >= -4
-- throughout the critical strip.
--
-- The claim is false: at |sigma-beta|=1/3 the contribution is -9,
-- so the asserted inequality would require 9 <= 4.
--
-- Below we give a constructive, postulate-free Agda proof that 9<=4
-- is impossible. The connection to -1/(1/3)^2 is standard elementary
-- rational arithmetic; this module does NOT model a zero of zeta,
-- prove an RH counterexample or prove anything about actual zeros.
--
-- Use as a fail-closed counterexample to the PROPOSED ESTIMATE only.
-- The true RH G3/off-line zero exclusion remains entirely open.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

data Empty : Set where

data _≤ⁿ_ : Nat → Nat → Set where
  zeroBelow : ∀ {n} → zero ≤ⁿ n
  successorBelow : ∀ {m n} → m ≤ⁿ n → suc m ≤ⁿ suc n

-- Reciprocal-square arithmetic at rational separation 1/3.
threeSquaredIsNine : 3 * 3 ≡ 9
threeSquaredIsNine = refl

-- 9 <= 4 would require 5 <= 0 after four successor cancellations.
nineCannotBeAtMostFour : 9 ≤ⁿ 4 → Empty
nineCannotBeAtMostFour
  (successorBelow (successorBelow
    (successorBelow (successorBelow ()))))

-- This does not use postulates, excluded middle, floating point, any
-- synthetic zero configuration or any unproved positivity compiler.
