module DASHI.Arithmetic.TwinPrimeProperPowerRectangleBoundExact where

------------------------------------------------------------------------
-- CT10 COMPOSED RECTANGULAR ENVELOPE FOR ALL PROPER PRIME POWERS
--
-- Reuses BOTH existing verified-in-source Nat arithmetic owners:
--  * FiniteNatFloorSquareRootExact.floorSquareRoot
--  * RiemannPrimePowerArithmetic.natPow
-- and the new CT10a/CT10b lemmas, rather than duplicating proofs.
--
-- A base >=2 is enough; no primality needs to be synthesized.
-- Any b^(k+2)<=U lies in the rectangle
--     b <= floor sqrt(U),  2^(k+2) <= U.
-- Counting the exponent coordinate by floor log2 U is a
-- SEPARATE CT11 cardinality proof; these are the exact bounds.
-- Source-written, pending Agda kernel check, 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)
open import DASHI.Analysis.RiemannPrimePowerArithmetic using (natPow)
open import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact
  using (floorSquareRoot)
import DASHI.Arithmetic.TwinPrimeProperPowerFloorRootBoundExact as Root
import DASHI.Arithmetic.TwinPrimeProperPowerBinaryExponentLowerExact as Binary

record ProperPowerRectangle (base k upper : Nat) : Set where
  constructor proper-power-rectangle
  field
    baseAtMostRoot : base ≤ floorSquareRoot upper
    binaryExponentPowerAtMostUpper : natPow 2 (suc (suc k)) ≤ upper
open ProperPowerRectangle public

properPowerInRectangle :
  (basePredecessor k upper : Nat) →
  natPow (suc (suc basePredecessor)) (suc (suc k)) ≤ upper →
  ProperPowerRectangle (suc (suc basePredecessor)) k upper
properPowerInRectangle basePredecessor k upper bound =
  proper-power-rectangle
    (Root.properPowerBaseLeFloorRoot
      (suc basePredecessor) k upper bound)
    (Binary.properPowerBinaryCeiling
      basePredecessor k upper bound)
