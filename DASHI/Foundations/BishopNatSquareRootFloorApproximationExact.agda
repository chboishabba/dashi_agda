module DASHI.Foundations.BishopNatSquareRootFloorApproximationExact where

------------------------------------------------------------------------
-- CANONICAL FLOOR APPROXIMANTS FOR sqrt(N)
--
-- For precision n > 0 define
--
--   T(N,n) = N * n * n
--   k(N,n) = floorSquareRoot(T(N,n))
--   a(N,n) = k(N,n) / n.
--
-- The finite Nat owner immediately gives
--
--   k(N,n)^2 <= N n^2 <= (k(N,n)+1)^2.
--
-- This is the exact arithmetic content required for the rational interval
--
--   a(N,n)^2 <= N <= (a(N,n)+1/n)^2.
--
-- Rational-order transport and the cross-precision Bishop regularity estimate
-- are intentionally kept as the next layer.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; _/_)

import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as Vendored
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Floor
open import DASHI.Physics.YangMills.CompactLieProofLevel

scaledSquareTarget : Nat → Nat → Nat
scaledSquareTarget radicand precision =
  radicand * precision * precision

floorSquareRootNumerator : Nat → Nat → Nat
floorSquareRootNumerator radicand precision =
  Floor.floorSquareRoot (scaledSquareTarget radicand precision)

floorSquareRootApproximation : Nat → Nat → ℚᵘ
floorSquareRootApproximation radicand zero = 0ℚᵘ
floorSquareRootApproximation radicand (suc precision) =
  + floorSquareRootNumerator radicand (suc precision) / suc precision

floorNumeratorSquareBelowScaledTarget :
  (radicand precision : Nat) →
  floorSquareRootNumerator radicand precision
    * floorSquareRootNumerator radicand precision
  ≤ scaledSquareTarget radicand precision
floorNumeratorSquareBelowScaledTarget radicand precision =
  Floor.floorSquareRootSquareBelow
    (scaledSquareTarget radicand precision)

scaledTargetBelowSuccessorNumeratorSquare :
  (radicand precision : Nat) →
  scaledSquareTarget radicand precision
  ≤ suc (floorSquareRootNumerator radicand precision)
      * suc (floorSquareRootNumerator radicand precision)
scaledTargetBelowSuccessorNumeratorSquare radicand precision =
  Floor.floorSquareRootNextSquareAbove
    (scaledSquareTarget radicand precision)

floorApproximationNatSandwichLevel : ProofLevel
floorApproximationNatSandwichLevel = machineChecked

------------------------------------------------------------------------
-- Frontier decomposition:
--
-- 1. transport the two Nat inequalities through rational division by n^2;
-- 2. prove 0 <= a(N,n);
-- 3. prove |a(N,m)-a(N,n)| <= 1/m + 1/n;
-- 4. package the result as BishopNatSquareRootApproximation N.
--
-- Step 4 then realizes an actual `Real.ℝ` through the pinned vendor/bishop
-- constructor already wrapped by BishopRegularRationalApproximationExact.
------------------------------------------------------------------------
