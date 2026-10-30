module DASHI.Arithmetic.TwinPrimeProperPowerFloorRootBoundExact where

------------------------------------------------------------------------
-- CT10a: A PROPER PRIME POWER HAS BASE <= FLOOR SQRT TARGET.
--
-- Original proof owners (import, never copy):
-- RiemannPrimePowerArithmetic.natPow
-- FiniteNatFloorSquareRootExact.floorSquareRootUpToMaximal
--
-- Only assumes a positive Nat base (suc b), MORE GENERAL than
-- requiring a certified prime. For every exponent >=2, the
-- bound (suc b)^(k+2) <= U entails suc b <= floorSquareRoot U.
--
-- This is elementary source-written proof, kernel pending.
-- It does NOT assert a pair-correlation bound or twin infinitude.
-- No ESD surfaces or external/Monster object authority.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)

import DASHI.Analysis.RiemannPrimePowerArithmetic as Power
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Root

powTwoEqualsSquare :
  (base : Nat) →
  Power.natPow base (suc (suc zero)) ≡ base * base
powTwoEqualsSquare base =
  cong (base *_) (NP.*-identityʳ base)

powNextAtLeastPrevious :
  (basePredecessor exponent : Nat) →
  Power.natPow (suc basePredecessor) exponent
    ≤ Power.natPow (suc basePredecessor) (suc exponent)
powNextAtLeastPrevious basePredecessor exponent =
  subst
    (λ x → Power.natPow (suc basePredecessor) exponent ≤ x)
    (NP.*-comm
      (Power.natPow (suc basePredecessor) exponent)
      (suc basePredecessor))
    (NP.m≤m*n
      (Power.natPow (suc basePredecessor) exponent)
      (suc basePredecessor))

squareBelowEveryProperPower :
  (basePredecessor k : Nat) →
  suc basePredecessor * suc basePredecessor
    ≤ Power.natPow (suc basePredecessor) (suc (suc k))
squareBelowEveryProperPower basePredecessor zero =
  subst
    (λ x → suc basePredecessor * suc basePredecessor ≤ x)
    (sym (powTwoEqualsSquare (suc basePredecessor)))
    NP.≤-refl
squareBelowEveryProperPower basePredecessor (suc k) =
  NP.≤-trans
    (squareBelowEveryProperPower basePredecessor k)
    (powNextAtLeastPrevious basePredecessor (suc (suc k)))

properPowerBaseLeFloorRoot :
  (basePredecessor k target : Nat) →
  Power.natPow (suc basePredecessor) (suc (suc k)) ≤ target →
  suc basePredecessor ≤ Root.floorSquareRoot target
properPowerBaseLeFloorRoot basePredecessor k target powerBound =
  Root.floorSquareRootUpToMaximal
    {target = target}
    {bound = suc target}
    {candidate = suc basePredecessor}
    (NP.≤-trans
      (Root.positiveSquareRootLeTarget squareBound)
      (NP.n≤1+n target))
    squareBound
  where
    squareBound :
      suc basePredecessor * suc basePredecessor ≤ target
    squareBound =
      NP.≤-trans
        (squareBelowEveryProperPower basePredecessor k)
        powerBound

-- Owned original all-prime carrier version:
-- a certified p^(k+2) automatically inherits this Nat bound
-- after rewriting the number p = toNat of the original carrier.
-- (No separate primality assumption was required above.)
