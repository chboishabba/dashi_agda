module DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact where

------------------------------------------------------------------------
-- POSITIVE NAT FRACTION ORDER
--
-- `Data.Rational.Unnormalised` defines rational order by integer
-- cross-multiplication.  For positive natural denominators we expose the
-- corresponding direct bridge:
--
--   a*d <= b*c  ==>  a/c <= b/d.
--
-- This is useful whenever a finite Nat certificate should be transported to
-- the same rational representation used by the vendored Bishop real carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Integer.Base as ℤ using (+_; +≤+)
open import Data.Nat.Base using (NonZero; _≤_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_; _≤_; *≤*)

open import DASHI.Physics.YangMills.CompactLieProofLevel

natFractionLe :
  ∀ {a b c d : Nat} →
  .{{_ : NonZero c}} →
  .{{_ : NonZero d}} →
  a * d ≤ b * c →
  (+ a / c) ℚ.≤ (+ b / d)
natFractionLe bound =
  ℚ.*≤* (ℤ.+≤+ bound)

natFractionOrderLevel : ProofLevel
natFractionOrderLevel = machineChecked

------------------------------------------------------------------------
-- This theorem is representation-level only: it exposes the exact
-- cross-product definition already used by unnormalised rationals.
------------------------------------------------------------------------
