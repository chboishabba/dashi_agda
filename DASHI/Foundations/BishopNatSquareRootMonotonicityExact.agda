module DASHI.Foundations.BishopNatSquareRootMonotonicityExact where

------------------------------------------------------------------------
-- MONOTONICITY OF THE CONSTRUCTED CANONICAL BISHOP NAT SQUARE ROOT
--
-- This is domain-neutral.  The finite floor-square-root numerator is monotone
-- in the Nat radicand; hence every positive-precision rational approximant is
-- pointwise monotone.  BishopPointwiseApproximationOrderExact then transports
-- that stronger pointwise order through the pinned vendor/bishop Real order.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_; NonZero)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using (_≤_)
import Real as BishopReal

import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Floor
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Fraction
import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as FloorApprox
import DASHI.Foundations.BishopNatSquareRootRationalCrossPrecisionExact as Cross
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Root
import DASHI.Foundations.BishopPointwiseApproximationOrderExact as Order

floorSquareRootMonotone :
  ∀ {left right : Nat} →
  left ≤ right →
  Floor.floorSquareRoot left ≤ Floor.floorSquareRoot right
floorSquareRootMonotone {left} {right} left≤right =
  Floor.floorSquareRootUpToMaximal
    {target = right}
    {bound = suc right}
    {candidate = Floor.floorSquareRoot left}
    candidateWithinBound
    candidateSquareFits
  where
  candidateWithinBound : Floor.floorSquareRoot left ≤ suc right
  candidateWithinBound =
    NatP.≤-trans
      (Floor.floorSquareRootLeTarget left)
      (NatP.≤-step left≤right)

  candidateSquareFits :
    Floor.floorSquareRoot left * Floor.floorSquareRoot left ≤ right
  candidateSquareFits =
    NatP.≤-trans
      (Floor.floorSquareRootSquareBelow left)
      left≤right

scaledSquareTargetMonotone :
  ∀ {left right precision : Nat} →
  left ≤ right →
  FloorApprox.scaledSquareTarget left precision
  ≤ FloorApprox.scaledSquareTarget right precision
scaledSquareTargetMonotone {left} {right} {precision} left≤right =
  NatP.*-mono-≤
    (NatP.*-mono-≤ left≤right NatP.≤-refl)
    NatP.≤-refl

floorSquareRootNumeratorMonotone :
  ∀ {left right precision : Nat} →
  left ≤ right →
  FloorApprox.floorSquareRootNumerator left precision
  ≤ FloorApprox.floorSquareRootNumerator right precision
floorSquareRootNumeratorMonotone left≤right =
  floorSquareRootMonotone (scaledSquareTargetMonotone left≤right)

canonicalFloorApproximationMonotone :
  ∀ {left right precision : Nat} →
  .{{_ : NonZero precision}} →
  left ≤ right →
  Cross.floorApproximationFraction left precision
  ℚ.≤ Cross.floorApproximationFraction right precision
canonicalFloorApproximationMonotone {precision = precision} left≤right =
  Fraction.natFractionLe
    (floorSquareRootNumeratorMonotone
      {precision = precision} left≤right)

canonicalFloorSquareRootRealMonotone :
  ∀ {left right : Nat} →
  left ≤ right →
  BishopReal._≤_
    (Root.canonicalFloorSquareRootReal left)
    (Root.canonicalFloorSquareRootReal right)
canonicalFloorSquareRootRealMonotone {left} {right} left≤right =
  Order.pointwiseApproximationOrderRealizesBishopOrder
    (Root.canonicalRegularApproximation left)
    (Root.canonicalRegularApproximation right)
    (λ precision →
      canonicalFloorApproximationMonotone
        {left = left} {right = right} {precision = precision} left≤right)
