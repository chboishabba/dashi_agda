module DASHI.Foundations.BishopNatSquareRootRegularFloorExact where

------------------------------------------------------------------------
-- REGULARITY OF THE CANONICAL FLOOR-SQUARE-ROOT APPROXIMANTS
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base as ℤ using (+_; +≤+)
open import Data.Nat.Base using (NonZero; z≤n)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; _/_; _+_; _-_; _≤_; ∣_∣; NonNegative; nonNegative; *≤*)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as FloorApprox
import DASHI.Foundations.BishopNatSquareRootRationalCrossPrecisionExact as Cross
import DASHI.Foundations.BishopRegularRationalApproximationExact as Approx
import DASHI.Foundations.RationalDirectedDifferenceAbsoluteBoundExact as Absolute
import DASHI.Mathematics.NumberTheory.FiniteNatSuccessorFractionExact as Successor
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneOverNat :
  (n : Nat) → .{{_ : NonZero n}} → ℚᵘ
oneOverNat n = + 1 / n

oneOverNatNonnegative :
  (n : Nat) → .{{_ : NonZero n}} →
  NonNegative (oneOverNat n)
oneOverNatNonnegative n =
  ℚ.nonNegative
    (ℚ.*≤* (ℤ.+≤+ z≤n))

floorApproximationDirectedRight :
  (radicand leftPrecision rightPrecision : Nat) →
  .{{_ : NonZero leftPrecision}} →
  .{{_ : NonZero rightPrecision}} →
  Cross.floorApproximationFraction radicand leftPrecision
  ℚ.≤
  Cross.floorApproximationFraction radicand rightPrecision
    ℚ.+ oneOverNat rightPrecision
floorApproximationDirectedRight radicand leftPrecision rightPrecision =
  ℚP.≤-respʳ-≃
    (Successor.successorFractionEquivalent
      (FloorApprox.floorSquareRootNumerator radicand rightPrecision)
      rightPrecision)
    (Cross.floorApproximationCrossPrecisionLe
      radicand leftPrecision rightPrecision)

floorApproximationDirectedLeft :
  (radicand leftPrecision rightPrecision : Nat) →
  .{{_ : NonZero leftPrecision}} →
  .{{_ : NonZero rightPrecision}} →
  Cross.floorApproximationFraction radicand rightPrecision
  ℚ.≤
  Cross.floorApproximationFraction radicand leftPrecision
    ℚ.+ oneOverNat leftPrecision
floorApproximationDirectedLeft radicand leftPrecision rightPrecision =
  ℚP.≤-respʳ-≃
    (Successor.successorFractionEquivalent
      (FloorApprox.floorSquareRootNumerator radicand leftPrecision)
      leftPrecision)
    (Cross.floorApproximationCrossPrecisionLeSwapped
      radicand leftPrecision rightPrecision)

floorApproximationRegular :
  (radicand leftPrecision rightPrecision : Nat) →
  .{{_ : NonZero leftPrecision}} →
  .{{_ : NonZero rightPrecision}} →
  ℚ.∣ Cross.floorApproximationFraction radicand leftPrecision
      ℚ.- Cross.floorApproximationFraction radicand rightPrecision ∣
  ℚ.≤
  (oneOverNat leftPrecision ℚ.+ oneOverNat rightPrecision)
floorApproximationRegular radicand leftPrecision rightPrecision =
  let
    instance
      leftNonnegative : NonNegative (oneOverNat leftPrecision)
      leftNonnegative = oneOverNatNonnegative leftPrecision

      rightNonnegative : NonNegative (oneOverNat rightPrecision)
      rightNonnegative = oneOverNatNonnegative rightPrecision
  in
  Absolute.absoluteDifferenceBound
    (floorApproximationDirectedRight
      radicand leftPrecision rightPrecision)
    (floorApproximationDirectedLeft
      radicand leftPrecision rightPrecision)

canonicalRegularApproximation :
  (radicand : Nat) → Approx.BishopRegularRationalApproximation
canonicalRegularApproximation radicand = record
  { approximation = Cross.floorApproximationFraction radicand
  ; regular = floorApproximationRegular radicand
  }

canonicalFloorSquareRootReal :
  Nat → BishopReal.ℝ
canonicalFloorSquareRootReal radicand =
  Approx.realizeRegularApproximation
    (canonicalRegularApproximation radicand)

bishopFloorSquareRootRegularityLevel : ProofLevel
bishopFloorSquareRootRegularityLevel = machineChecked
