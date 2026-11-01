module DASHI.Physics.Closure.NSTriadKNBishopNatRootCriticalMultiplierBoundaryRound519Exact where

------------------------------------------------------------------------
-- ROUND519 / BISHOP NAT ROOT -> CRITICAL MULTIPLIER BOUNDARY
--
-- R518 closes the exact squared-radius annulus on the canonical dyadic shell.
-- The repository also owns a CONSTRUCTED Bishop-real square root for every Nat
-- radicand, together with nonnegativity and the semantic square law
--
--   sqrtNat(n) * sqrtNat(n) ~= n.
--
-- The formerly open scalar bridge
--
--   m <= n  ->  sqrtNat(m) <= sqrtNat(n)
--
-- is now closed by the domain-neutral Foundations theorem
-- BishopNatSquareRootMonotonicityExact.  That theorem descends to the canonical
-- rational floor-root approximants, proves pointwise order, and realizes that
-- order through the pinned vendor/bishop Real representation.
--
-- Thus R518's squared annulus now lifts modewise to the physical
-- half-derivative multiplier.  The remaining whole-norm work is only finite
-- Fourier-sum transport, not square-root existence or monotonicity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal

import DASHI.Foundations.BishopNatSquareRootApproximationExact as Approximation
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Root
import DASHI.Foundations.BishopNatSquareRootNonnegativeExact as RootNN
import DASHI.Foundations.BishopNatSquareRootSemanticSquareExact as RootSquare
import DASHI.Foundations.BishopNatSquareRootMonotonicityExact as RootMono
import DASHI.Physics.Closure.NSTriadKNCanonicalDyadicEuclideanAnnulusRound518Exact as R518

sqrtNat : Nat → BishopReal.ℝ
sqrtNat = Root.canonicalFloorSquareRootReal

canonicalNatRootNonnegative :
  (n : Nat) → BishopReal.NonNegative (sqrtNat n)
canonicalNatRootNonnegative = RootNN.canonicalFloorSquareRootNonnegative

canonicalNatRootSquaresToNat :
  (n : Nat) →
  BishopReal._≃_
    (BishopReal._*_ (sqrtNat n) (sqrtNat n))
    (BishopReal._⋆ (Approximation.natAsRational n))
canonicalNatRootSquaresToNat = RootSquare.canonicalFloorSquareRootSquaresToNat

record CanonicalNatRootMonotonicity : Set where
  constructor canonical-nat-root-monotonicity
  field
    monotone :
      ∀ {m n : Nat} →
      m ≤ n →
      BishopReal._≤_ (sqrtNat m) (sqrtNat n)

open CanonicalNatRootMonotonicity public

canonicalNatRootMonotonicity : CanonicalNatRootMonotonicity
canonicalNatRootMonotonicity = record
  { monotone = RootMono.canonicalFloorSquareRootRealMonotone }

record ModewiseCriticalMultiplierComparison
    (lowerSquared physicalSquared upperSquared : Nat) : Set where
  constructor modewise-critical-multiplier-comparison
  field
    lowerSquareBelowPhysical : lowerSquared ≤ physicalSquared
    physicalSquareBelowUpper : physicalSquared ≤ upperSquared
    lowerRootBelowPhysical :
      BishopReal._≤_ (sqrtNat lowerSquared) (sqrtNat physicalSquared)
    physicalRootBelowUpper :
      BishopReal._≤_ (sqrtNat physicalSquared) (sqrtNat upperSquared)

open ModewiseCriticalMultiplierComparison public

monotonicityLiftsSquaredComparison :
  (M : CanonicalNatRootMonotonicity) →
  ∀ {lowerSquared physicalSquared upperSquared} →
  lowerSquared ≤ physicalSquared →
  physicalSquared ≤ upperSquared →
  ModewiseCriticalMultiplierComparison
    lowerSquared physicalSquared upperSquared
monotonicityLiftsSquaredComparison M lower≤physical physical≤upper = record
  { lowerSquareBelowPhysical = lower≤physical
  ; physicalSquareBelowUpper = physical≤upper
  ; lowerRootBelowPhysical = monotone M lower≤physical
  ; physicalRootBelowUpper = monotone M physical≤upper
  }

canonicalModewiseCriticalMultiplierComparison :
  ∀ {lowerSquared physicalSquared upperSquared} →
  lowerSquared ≤ physicalSquared →
  physicalSquared ≤ upperSquared →
  ModewiseCriticalMultiplierComparison
    lowerSquared physicalSquared upperSquared
canonicalModewiseCriticalMultiplierComparison =
  monotonicityLiftsSquaredComparison canonicalNatRootMonotonicity

------------------------------------------------------------------------
-- Status / first missing coordinate.
------------------------------------------------------------------------

round519CanonicalNatRootConstructed : Bool
round519CanonicalNatRootConstructed = true

round519CanonicalNatRootNonnegativeClosed : Bool
round519CanonicalNatRootNonnegativeClosed = true

round519CanonicalNatRootSemanticSquareClosed : Bool
round519CanonicalNatRootSemanticSquareClosed = true

round519CanonicalNatRootMonotonicityClosed : Bool
round519CanonicalNatRootMonotonicityClosed = true

round519R518SquaredAnnulusClosed : Bool
round519R518SquaredAnnulusClosed =
  R518.round518CanonicalDyadicEuclideanSquaredAnnulusClosed

round519RemainingCoordinateIsNatRootMonotonicity : Bool
round519RemainingCoordinateIsNatRootMonotonicity = false

round519RemainingCoordinateIsFiniteFourierSumTransport : Bool
round519RemainingCoordinateIsFiniteFourierSumTransport = true

round519ClayPromotion : Bool
round519ClayPromotion = false

round519CanonicalNatRootConstructedIsTrue :
  round519CanonicalNatRootConstructed ≡ true
round519CanonicalNatRootConstructedIsTrue = refl

round519CanonicalNatRootNonnegativeClosedIsTrue :
  round519CanonicalNatRootNonnegativeClosed ≡ true
round519CanonicalNatRootNonnegativeClosedIsTrue = refl

round519CanonicalNatRootSemanticSquareClosedIsTrue :
  round519CanonicalNatRootSemanticSquareClosed ≡ true
round519CanonicalNatRootSemanticSquareClosedIsTrue = refl

round519CanonicalNatRootMonotonicityClosedIsTrue :
  round519CanonicalNatRootMonotonicityClosed ≡ true
round519CanonicalNatRootMonotonicityClosedIsTrue = refl

round519RemainingCoordinateIsNatRootMonotonicityIsFalse :
  round519RemainingCoordinateIsNatRootMonotonicity ≡ false
round519RemainingCoordinateIsNatRootMonotonicityIsFalse = refl

round519ClayPromotionIsFalse : round519ClayPromotion ≡ false
round519ClayPromotionIsFalse = refl
