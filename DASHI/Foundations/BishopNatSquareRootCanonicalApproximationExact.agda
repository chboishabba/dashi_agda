module DASHI.Foundations.BishopNatSquareRootCanonicalApproximationExact where

------------------------------------------------------------------------
-- CANONICAL CERTIFICATE FOR THE VENDORED BISHOP NAT SQUARE ROOT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Integer.Base as ℤ using (+_; +≤+)
open import Data.Nat.Base using (NonZero; z≤n)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; _/_; _+_; _*_; _≤_; NonNegative; nonNegative; *≤*)
import Data.Rational.Unnormalised.Properties as ℚP
import Real as BishopReal

import DASHI.Foundations.BishopNatSquareRootApproximationExact as Approximation
import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as Floor
import DASHI.Foundations.BishopNatSquareRootRationalCrossPrecisionExact as Cross
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Regular
import DASHI.Mathematics.NumberTheory.FiniteNatSuccessorFractionExact as Successor
open import DASHI.Physics.YangMills.CompactLieProofLevel

canonicalApproximation :
  (radicand precision : Nat) → .{{_ : NonZero precision}} → ℚᵘ
canonicalApproximation radicand precision =
  Cross.floorApproximationFraction radicand precision

canonicalApproximationNonnegative :
  (radicand precision : Nat) → .{{_ : NonZero precision}} →
  0ℚᵘ ℚ.≤ canonicalApproximation radicand precision
canonicalApproximationNonnegative radicand precision =
  ℚ.*≤* (ℤ.+≤+ z≤n)

canonicalApproximationSquareBelow :
  (radicand precision : Nat) → .{{_ : NonZero precision}} →
  (canonicalApproximation radicand precision
    ℚ.* canonicalApproximation radicand precision)
  ℚ.≤ Approximation.natAsRational radicand
canonicalApproximationSquareBelow radicand precision =
  ℚ.*≤*
    (ℤ.+≤+
      (Floor.floorNumeratorSquareBelowScaledTarget
        radicand precision))

successorApproximation :
  (radicand precision : Nat) → .{{_ : NonZero precision}} → ℚᵘ
successorApproximation radicand precision =
  + suc (Floor.floorSquareRootNumerator radicand precision) / precision

radicandBelowSuccessorApproximationSquare :
  (radicand precision : Nat) → .{{_ : NonZero precision}} →
  Approximation.natAsRational radicand
  ℚ.≤
  (successorApproximation radicand precision
    ℚ.* successorApproximation radicand precision)
radicandBelowSuccessorApproximationSquare radicand precision =
  ℚ.*≤*
    (ℤ.+≤+
      (Floor.scaledTargetBelowSuccessorNumeratorSquare
        radicand precision))

successorApproximationEquivalentUpper :
  (radicand precision : Nat) → .{{_ : NonZero precision}} →
  successorApproximation radicand precision
  ℚ.≃
  (canonicalApproximation radicand precision ℚ.+ (+ 1 / precision))
successorApproximationEquivalentUpper radicand precision =
  Successor.successorFractionEquivalent
    (Floor.floorSquareRootNumerator radicand precision)
    precision

radicandBelowCanonicalUpperSquare :
  (radicand precision : Nat) → .{{_ : NonZero precision}} →
  Approximation.natAsRational radicand
  ℚ.≤
  ((canonicalApproximation radicand precision ℚ.+ (+ 1 / precision))
    ℚ.*
   (canonicalApproximation radicand precision ℚ.+ (+ 1 / precision)))
radicandBelowCanonicalUpperSquare radicand precision =
  ℚP.≤-respʳ-≃
    (ℚP.*-cong
      (successorApproximationEquivalentUpper radicand precision)
      (successorApproximationEquivalentUpper radicand precision))
    (radicandBelowSuccessorApproximationSquare radicand precision)

canonicalNatSquareRootApproximation :
  (radicand : Nat) →
  Approximation.BishopNatSquareRootApproximation radicand
canonicalNatSquareRootApproximation radicand = record
  { regularApproximation = Regular.canonicalRegularApproximation radicand
  ; approximationNonnegative = canonicalApproximationNonnegative radicand
  ; approximationSquareBelowRadicand = canonicalApproximationSquareBelow radicand
  ; radicandBelowOneOverNUpperSquare =
      radicandBelowCanonicalUpperSquare radicand
  }

canonicalNatSquareRootCandidate : Nat → BishopReal.ℝ
canonicalNatSquareRootCandidate radicand =
  Approximation.bishopNatSquareRootCandidate
    (canonicalNatSquareRootApproximation radicand)

canonicalNatSquareRootCandidateIsRegularFloor :
  (radicand : Nat) →
  canonicalNatSquareRootCandidate radicand
  ≡ Regular.canonicalFloorSquareRootReal radicand
canonicalNatSquareRootCandidateIsRegularFloor radicand = refl

canonicalNatSquareRootApproximationLevel : ProofLevel
canonicalNatSquareRootApproximationLevel = machineChecked
