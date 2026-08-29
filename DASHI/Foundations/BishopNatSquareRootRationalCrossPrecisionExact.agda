module DASHI.Foundations.BishopNatSquareRootRationalCrossPrecisionExact where

------------------------------------------------------------------------
-- RATIONAL CROSS-PRECISION OVERLAP FOR THE CANONICAL FLOOR APPROXIMANTS
--
-- The finite Nat theorem already proves
--
--   k_m * n <= (k_n + 1) * m.
--
-- Unnormalised rational order is defined by exactly this cross multiplication,
-- so for positive precisions we obtain
--
--   k_m/m <= (k_n+1)/n
--
-- and its swapped companion with no analytic input.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_; _≤_)

import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as FloorApprox
import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as Vendored
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Fraction
open import DASHI.Physics.YangMills.CompactLieProofLevel

floorApproximationFraction :
  (radicand precision : Nat) →
  .{{_ : NonZero precision}} →
  ℚᵘ
floorApproximationFraction radicand precision =
  + FloorApprox.floorSquareRootNumerator radicand precision / precision

successorFloorApproximationFraction :
  (radicand precision : Nat) →
  .{{_ : NonZero precision}} →
  ℚᵘ
successorFloorApproximationFraction radicand precision =
  + suc (FloorApprox.floorSquareRootNumerator radicand precision) / precision

floorApproximationCrossPrecisionLe :
  (radicand leftPrecision rightPrecision : Nat) →
  .{{_ : NonZero leftPrecision}} →
  .{{_ : NonZero rightPrecision}} →
  floorApproximationFraction radicand leftPrecision
  ℚ.≤
  successorFloorApproximationFraction radicand rightPrecision
floorApproximationCrossPrecisionLe radicand leftPrecision rightPrecision =
  Fraction.natFractionLe
    (FloorApprox.floorNumeratorCrossPrecision
      radicand leftPrecision rightPrecision)

floorApproximationCrossPrecisionLeSwapped :
  (radicand leftPrecision rightPrecision : Nat) →
  .{{_ : NonZero leftPrecision}} →
  .{{_ : NonZero rightPrecision}} →
  floorApproximationFraction radicand rightPrecision
  ℚ.≤
  successorFloorApproximationFraction radicand leftPrecision
floorApproximationCrossPrecisionLeSwapped radicand leftPrecision rightPrecision =
  Fraction.natFractionLe
    (FloorApprox.floorNumeratorCrossPrecisionSwapped
      radicand leftPrecision rightPrecision)

floorApproximationRationalCrossPrecisionLevel : ProofLevel
floorApproximationRationalCrossPrecisionLevel = machineChecked

------------------------------------------------------------------------
-- Next exact algebraic step:
--
--   (k+1)/n ≃ k/n + 1/n.
--
-- Together with the two inequalities above this yields the directed error
-- bounds required for Bishop regularity.
------------------------------------------------------------------------
