module DASHI.Arithmetic.TwinPrimeProperPowerCoreBinaryCapacityReuseExact where

------------------------------------------------------------------------
-- CT10 ↔ EXISTING CORE BINARY CAPACITY (REUSE, NOT REBUILD).
--
-- Original owner: DASHI.Core.GeneralResidualFibreCardinalityExact.pow2,
-- from future-safe finite residual cardinality. We reuse its NUMERIC
-- 2^k function only; this is NOT a same-object statement about
-- prime powers, quotient carriers or future-safe dynamics.
--
-- Original prime-power numeric owner:
-- DASHI.Analysis.RiemannPrimePowerArithmetic.natPow
-- Original CT10b inequality owner:
-- TwinPrimeProperPowerBinaryExponentLowerExact.
--
-- Source-written, Agda kernel pending. No ESD edits, no postulates.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst)

import DASHI.Core.GeneralResidualFibreCardinalityExact as Capacity
import DASHI.Analysis.RiemannPrimePowerArithmetic as Power
import DASHI.Arithmetic.TwinPrimeProperPowerBinaryExponentLowerExact as Binary

numericPowTwoEqualsCoreCapacity :
  (e : Nat) →
  Power.natPow 2 e ≡ Capacity.pow2 e
numericPowTwoEqualsCoreCapacity zero = refl
numericPowTwoEqualsCoreCapacity (suc e) =
  cong (2 *_) (numericPowTwoEqualsCoreCapacity e)

properPowerNeedsCoreBinaryCapacity :
  (basePredecessor k upper : Nat) →
  Power.natPow (suc (suc basePredecessor)) (suc (suc k))
    ≤ upper →
  Capacity.pow2 (suc (suc k)) ≤ upper
properPowerNeedsCoreBinaryCapacity basePredecessor k upper powerBound =
  subst
    (λ x → x ≤ upper)
    (numericPowTwoEqualsCoreCapacity (suc (suc k)))
    (Binary.properPowerBinaryCeiling
      basePredecessor k upper powerBound)
