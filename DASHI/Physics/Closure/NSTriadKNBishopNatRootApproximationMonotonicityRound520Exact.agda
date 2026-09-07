module DASHI.Physics.Closure.NSTriadKNBishopNatRootApproximationMonotonicityRound520Exact where

------------------------------------------------------------------------
-- ROUND520 / FINITE MONOTONICITY OF CANONICAL NAT-ROOT APPROXIMANTS
--
-- R519 isolated monotonicity of the constructed Bishop Nat root as the first
-- missing scalar-order coordinate.  All substantive number-theoretic content
-- can already be paid before entering the Bishop-real order:
--
--   left <= right
--     => floorSqrt(left) <= floorSqrt(right)
--     => floorSqrt(left*n^2) <= floorSqrt(right*n^2)
--     => a(left,n) <= a(right,n)
--
-- for every positive precision n.  The first implication follows only from
-- the finite floor-root maximality theorem: the left root is an admissible
-- candidate for the right target.
--
-- Thus after this round, the remaining R519 step is purely the standard
-- realization theorem that pointwise-ordered regular rational approximants
-- induce the corresponding Bishop-real order.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_; NonZero)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using (_≤_)

import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Floor
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Fraction
import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as Approx
import DASHI.Foundations.BishopNatSquareRootRationalCrossPrecisionExact as Cross
import DASHI.Physics.Closure.NSTriadKNBishopNatRootCriticalMultiplierBoundaryRound519Exact as R519

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
  candidateWithinBound :
    Floor.floorSquareRoot left ≤ suc right
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
  Approx.scaledSquareTarget left precision
  ≤ Approx.scaledSquareTarget right precision
scaledSquareTargetMonotone {left} {right} {precision} left≤right =
  NatP.*-mono-≤
    (NatP.*-mono-≤ left≤right NatP.≤-refl)
    NatP.≤-refl

floorSquareRootNumeratorMonotone :
  ∀ {left right precision : Nat} →
  left ≤ right →
  Approx.floorSquareRootNumerator left precision
  ≤ Approx.floorSquareRootNumerator right precision
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

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

round520FiniteFloorSquareRootMonotonicityClosed : Bool
round520FiniteFloorSquareRootMonotonicityClosed = true

round520ScaledTargetMonotonicityClosed : Bool
round520ScaledTargetMonotonicityClosed = true

round520CanonicalRationalApproximationMonotonicityClosed : Bool
round520CanonicalRationalApproximationMonotonicityClosed = true

round520BishopRealRootMonotonicityClosed : Bool
round520BishopRealRootMonotonicityClosed =
  R519.round519CanonicalNatRootMonotonicityClosed

round520RemainingCoordinateIsApproximationOrderRealization : Bool
round520RemainingCoordinateIsApproximationOrderRealization = true

round520ClayPromotion : Bool
round520ClayPromotion = false

round520FiniteFloorSquareRootMonotonicityClosedIsTrue :
  round520FiniteFloorSquareRootMonotonicityClosed ≡ true
round520FiniteFloorSquareRootMonotonicityClosedIsTrue = refl

round520CanonicalRationalApproximationMonotonicityClosedIsTrue :
  round520CanonicalRationalApproximationMonotonicityClosed ≡ true
round520CanonicalRationalApproximationMonotonicityClosedIsTrue = refl

round520BishopRealRootMonotonicityClosedIsFalse :
  round520BishopRealRootMonotonicityClosed ≡ false
round520BishopRealRootMonotonicityClosedIsFalse =
  R519.round519CanonicalNatRootMonotonicityClosedIsFalse

round520ClayPromotionIsFalse : round520ClayPromotion ≡ false
round520ClayPromotionIsFalse = refl
