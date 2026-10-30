module DASHI.Arithmetic.TwinPrimeProperPowerBinaryExponentLowerExact where

------------------------------------------------------------------------
-- CT10b: BINARY EXPONENT LOWER ENVELOPE FOR EVERY PRIME BASE.
--
-- Original Nat exponentiation: RiemannPrimePowerArithmetic.natPow.
-- A prime base is >=2.  For ANY b>=2 and e, 2^e<=b^e.
-- Thus if b^e <= U, the full exponent e is bounded by the
-- binary-log growth envelope of U. No analytic logarithm is used.
-- CT10a's square-root base bound is kept in its original module.
--
-- This is a genuine elementary conditional inequality. It does
-- not supply the finite number-of-exponents count or CT15.
-- Source-written / Agda kernel pending; 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
import DASHI.Analysis.RiemannPrimePowerArithmetic as Power

binaryPowerBelowPositiveBasePower :
  (basePredecessor exponent : Nat) →
  Power.natPow 2 exponent
    ≤ Power.natPow (suc (suc basePredecessor)) exponent
binaryPowerBelowPositiveBasePower basePredecessor zero =
  NP.≤-refl
binaryPowerBelowPositiveBasePower basePredecessor (suc exponent) =
  NP.*-mono-≤
    (s≤s (s≤s z≤n))
    (binaryPowerBelowPositiveBasePower basePredecessor exponent)

properPowerBinaryCeiling :
  (basePredecessor exponentExtra target : Nat) →
  Power.natPow (suc (suc basePredecessor))
    (suc (suc exponentExtra)) ≤ target →
  Power.natPow 2 (suc (suc exponentExtra)) ≤ target
properPowerBinaryCeiling basePredecessor exponentExtra target
    bound =
  NP.≤-trans
    (binaryPowerBelowPositiveBasePower basePredecessor
      (suc (suc exponentExtra)))
    bound
