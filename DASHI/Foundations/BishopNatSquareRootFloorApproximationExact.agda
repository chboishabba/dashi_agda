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
-- Cross-precision comparison is also finite arithmetic:
--
--   k(N,m) * n <= (k(N,n)+1) * m.
--
-- This is the numerator form of
--
--   a(N,m) <= a(N,n) + 1/n,
--
-- and, after swapping m/n, supplies Bishop regularity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; _/_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

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

------------------------------------------------------------------------
-- Polynomial normal forms used only to transport the substantive inequalities.

leftSquareProductIdentity :
  (left scale : Nat) →
  (left * scale) * (left * scale)
  ≡ (left * left) * (scale * scale)
leftSquareProductIdentity =
  solve 2
    (λ left scale →
      (left :* scale) :* (left :* scale)
      :=
      (left :* left) :* (scale :* scale))
    refl

scaledTargetsCommute :
  (radicand leftPrecision rightPrecision : Nat) →
  (scaledSquareTarget radicand leftPrecision)
    * (rightPrecision * rightPrecision)
  ≡
  (scaledSquareTarget radicand rightPrecision)
    * (leftPrecision * leftPrecision)
scaledTargetsCommute =
  solve 3
    (λ radicand leftPrecision rightPrecision →
      ((radicand :* leftPrecision) :* leftPrecision)
        :* (rightPrecision :* rightPrecision)
      :=
      ((radicand :* rightPrecision) :* rightPrecision)
        :* (leftPrecision :* leftPrecision))
    refl

------------------------------------------------------------------------
-- Cross-precision numerator comparison.

floorNumeratorCrossPrecision :
  (radicand leftPrecision rightPrecision : Nat) →
  floorSquareRootNumerator radicand leftPrecision * rightPrecision
  ≤
  suc (floorSquareRootNumerator radicand rightPrecision) * leftPrecision
floorNumeratorCrossPrecision radicand leftPrecision rightPrecision =
  Floor.squareOrderReflects squareComparison
  where
  leftRoot : Nat
  leftRoot = floorSquareRootNumerator radicand leftPrecision

  rightRootPlusOne : Nat
  rightRootPlusOne =
    suc (floorSquareRootNumerator radicand rightPrecision)

  leftScaledSquareBound :
    (leftRoot * leftRoot) * (rightPrecision * rightPrecision)
    ≤
    (scaledSquareTarget radicand leftPrecision)
      * (rightPrecision * rightPrecision)
  leftScaledSquareBound =
    NatP.*-mono-≤
      (floorNumeratorSquareBelowScaledTarget radicand leftPrecision)
      NatP.≤-refl

  rightScaledSquareBound :
    (scaledSquareTarget radicand rightPrecision)
      * (leftPrecision * leftPrecision)
    ≤
    (rightRootPlusOne * rightRootPlusOne)
      * (leftPrecision * leftPrecision)
  rightScaledSquareBound =
    NatP.*-mono-≤
      (scaledTargetBelowSuccessorNumeratorSquare
        radicand rightPrecision)
      NatP.≤-refl

  middleBound :
    (scaledSquareTarget radicand leftPrecision)
      * (rightPrecision * rightPrecision)
    ≤
    (scaledSquareTarget radicand rightPrecision)
      * (leftPrecision * leftPrecision)
  middleBound =
    NatP.≤-reflexive
      (scaledTargetsCommute radicand leftPrecision rightPrecision)

  rawSquareComparison :
    (leftRoot * leftRoot) * (rightPrecision * rightPrecision)
    ≤
    (rightRootPlusOne * rightRootPlusOne)
      * (leftPrecision * leftPrecision)
  rawSquareComparison =
    NatP.≤-trans
      leftScaledSquareBound
      (NatP.≤-trans middleBound rightScaledSquareBound)

  squareComparison :
    (leftRoot * rightPrecision) * (leftRoot * rightPrecision)
    ≤
    (rightRootPlusOne * leftPrecision)
      * (rightRootPlusOne * leftPrecision)
  squareComparison =
    subst
      (λ upper →
        (leftRoot * rightPrecision) * (leftRoot * rightPrecision)
        ≤ upper)
      (sym (leftSquareProductIdentity rightRootPlusOne leftPrecision))
      (subst
        (λ lower →
          lower
          ≤ (rightRootPlusOne * rightRootPlusOne)
              * (leftPrecision * leftPrecision))
        (sym (leftSquareProductIdentity leftRoot rightPrecision))
        rawSquareComparison)

floorNumeratorCrossPrecisionSwapped :
  (radicand leftPrecision rightPrecision : Nat) →
  floorSquareRootNumerator radicand rightPrecision * leftPrecision
  ≤
  suc (floorSquareRootNumerator radicand leftPrecision) * rightPrecision
floorNumeratorCrossPrecisionSwapped radicand leftPrecision rightPrecision =
  floorNumeratorCrossPrecision radicand rightPrecision leftPrecision

floorApproximationNatSandwichLevel : ProofLevel
floorApproximationNatSandwichLevel = machineChecked

floorApproximationCrossPrecisionLevel : ProofLevel
floorApproximationCrossPrecisionLevel = machineChecked

------------------------------------------------------------------------
-- Frontier decomposition:
--
-- 1. transport the Nat sandwich through rational division by n^2;
-- 2. transport cross-precision numerator bounds to rational order;
-- 3. derive |a(N,m)-a(N,n)| <= 1/m + 1/n;
-- 4. package the result as BishopNatSquareRootApproximation N.
--
-- Step 4 then realizes an actual `Real.ℝ` through the pinned vendor/bishop
-- constructor already wrapped by BishopRegularRationalApproximationExact.
------------------------------------------------------------------------
