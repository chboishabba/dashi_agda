module DASHI.Foundations.BishopNatSquareRootNonnegativeExact where

------------------------------------------------------------------------
-- NONNEGATIVITY OF THE CONSTRUCTED FLOOR-SQUARE-ROOT REAL
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base as ℤ using (+_; +≤+)
import Data.Nat.Base as Nat
open Nat using (NonZero; z≤n)
open import Data.Rational.Unnormalised as ℚ using
  (0ℚᵘ; _/_; -_; _≤_; *≤*)
import Data.Rational.Unnormalised.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Real as BishopReal
import DASHI.Foundations.BishopNatSquareRootRationalCrossPrecisionExact as Cross
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Regular
open import DASHI.Physics.YangMills.CompactLieProofLevel

floorApproximationNonnegative :
  (radicand precision : Nat) →
  .{{_ : NonZero precision}} →
  0ℚᵘ ℚ.≤ Cross.floorApproximationFraction radicand precision
floorApproximationNonnegative radicand precision =
  ℚ.*≤* (ℤ.+≤+ z≤n)

negativeOneOverNatBelowZero :
  (precision : Nat) →
  .{{_ : NonZero precision}} →
  ℚ.- (+ 1 / precision) ℚ.≤ 0ℚᵘ
negativeOneOverNatBelowZero precision =
  ℚP.p≤q⇒p-q≤0
    (ℚ.*≤* (ℤ.+≤+ z≤n))

canonicalFloorSquareRootNonnegative :
  (radicand : Nat) →
  BishopReal.NonNegative (Regular.canonicalFloorSquareRootReal radicand)
canonicalFloorSquareRootNonnegative radicand =
  BishopReal.nonNeg*
    (λ precision {precision≢0} →
      let
        instance
          precisionNonZero : NonZero precision
          precisionNonZero = Nat.≢-nonZero precision≢0
      in
      ℚP.≤-trans
        (negativeOneOverNatBelowZero precision)
        (floorApproximationNonnegative radicand precision))

bishopNatSquareRootNonnegativeLevel : ProofLevel
bishopNatSquareRootNonnegativeLevel = machineChecked
