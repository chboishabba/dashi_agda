{-# OPTIONS --safe #-}
module DASHI.Arithmetic.TwinPrimeStrongWeakMaxCutBidiExact where

-- 2026-10-31. Exact constructive logical bridge at the two proposed
-- correlation max cuts. Existing real Mangoldt/prime-power analytics
-- are NOT asserted here. This module uses genuine certified Nat primes
-- from TwinPrimeSixWheelExact and bounded finite interval witnesses
-- from TwinPrimeMangoldtNonzeroPrimeSumWitnessExact.
-- Existing theorem owners and mathematical provenance are retained.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _×_; _,_)
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import DASHI.Arithmetic.TwinPrimeMangoldtNonzeroPrimeSumWitnessExact as Witness
import Data.Nat.Properties as NP

-- The exact weak research target, stripped of numerical representation:
-- every lower cutoff admits a later interval with a certified twin pair.
CofinalTwinWindow : Set
CofinalTwinWindow =
  (N : Nat) →
  Σ Nat (λ start →
    (N ≤ start) ×
    Σ Nat (λ count → Witness.TwinInInterval start count))

-- The repo's original definition uses true Nat prime certificates.
cofinalWindowToTwinInfinitude :
  CofinalTwinWindow → Twin.TwinPrimesInfinitelyOften
cofinalWindowToTwinInfinitude windows N with windows N
... | start , (late , (count , observed)) =
  lift start late count observed
  where
  lift :
    (start : Nat) → N ≤ start → (count : Nat) →
    Witness.TwinInInterval start count →
    Σ Nat (λ p → (N ≤ p) × Twin.TwinPrimeAt p)
  lift start late count observed
    with Witness.twinInIntervalReadout observed
  ... | p , (afterStart , twin) =
    p , (NP.≤-trans late afterStart , twin)

-- A singleton starting at each certified twin supplies an interval.
twinInfinitudeToCofinalWindow :
  Twin.TwinPrimesInfinitelyOften → CofinalTwinWindow
twinInfinitudeToCofinalWindow twins N with twins N
... | p , (late , twin) =
  p , (late , suc (zero) ,
    Witness.here twin)

-- Formal analytical endpoint contracts kept as separate parameters.
-- Sufficient STRONG target: total classical real Mangoldt correlation
-- S(X) has a uniform positive linear lower bound and proper-power
-- E(X)=o(X). Its use additionally requires the actual real order,
-- asymptotic definitions, and translation into cofinal witnesses.
--
-- Equivalent WEAK target: real prime-only P(X)=S(X)-E(X)
-- is unbounded, or cofinally nonzero actual prime-only intervals.
-- Its transport requires actual Nat prime ownership and strictly
-- positive real logarithm weights; generic Weil scalars alone do
-- not supply this.
--
-- In particular no proof of either analytic target is given here.
