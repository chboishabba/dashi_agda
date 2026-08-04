module DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_!)
open import Data.Nat.Properties using (_!≢0)
open import Data.Rational.Unnormalised using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProps
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as HalfBall

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Constructive-real inhabitants for the round-six Bishop cutset.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- IMPORTANT REPRESENTATION CORRECTION
--
-- Data.Rational.Unnormalised.mkℚᵘ stores `denominator - 1`.  The former
-- definition
--
--   mkℚᵘ (+ 1) (factorial n)
--
-- therefore represented 1/(n!+1), not 1/n!.  The corrected definition uses
-- the public division constructor together with the standard-library proof
-- that n! is nonzero.
--
-- The odd/even index functions are recursive rather than solver-normalized.
-- This makes the two-step exponent and factorial recurrences definitionally
-- visible to Agda while retaining exactly the sequences 2k+1 and 2k.
------------------------------------------------------------------------

half quarter oneTwentyFourth oneEighth : ℚᵘ
half = + 1 / 2
quarter = + 1 / 4
oneTwentyFourth = + 1 / 24
oneEighth = + 1 / 8

two : Nat
two = suc (suc zero)

oddExponent evenExponent : Nat → Nat
oddExponent zero = suc zero
oddExponent (suc n) = suc (suc (oddExponent n))
evenExponent zero = zero
evenExponent (suc n) = suc (suc (evenExponent n))

oddExponentSuccessor : ∀ n →
  oddExponent (suc n) ≡ suc (suc (oddExponent n))
oddExponentSuccessor n = refl

evenExponentSuccessor : ∀ n →
  evenExponent (suc n) ≡ suc (suc (evenExponent n))
evenExponentSuccessor n = refl

factorial : Nat → Nat
factorial n = n !

factorialZero : factorial zero ≡ suc zero
factorialZero = refl

factorialSuccessor :
  ∀ n → factorial (suc n) ≡ suc n * factorial n
factorialSuccessor n = refl

factorialTwoStep :
  ∀ n →
  factorial (suc (suc n))
  ≡ suc (suc n) * (suc n * factorial n)
factorialTwoStep n = refl

oddFactorialSuccessor :
  ∀ n →
  factorial (oddExponent (suc n))
  ≡ suc (suc (oddExponent n))
      * (suc (oddExponent n) * factorial (oddExponent n))
oddFactorialSuccessor n = refl

evenFactorialSuccessor :
  ∀ n →
  factorial (evenExponent (suc n))
  ≡ suc (suc (evenExponent n))
      * (suc (evenExponent n) * factorial (evenExponent n))
evenFactorialSuccessor n = refl

inverseFactorialRational : Nat → ℚᵘ
inverseFactorialRational n = + 1 / (n !)
  where
  instance
    factorialNonZero = n !≢0

square : BishopReal.ℝ → BishopReal.ℝ
square x = x BishopReal.* x

halfBallSquareBelowQuarter : Set
halfBallSquareBelowQuarter =
  ∀ {x : BishopReal.ℝ} →
  BishopReal.∣ x ∣ BishopReal.≤ half BishopReal.⋆ →
  square x BishopReal.≤ quarter BishopReal.⋆

halfBallSquareBelowQuarterProof : halfBallSquareBelowQuarter
halfBallSquareBelowQuarterProof {x} insideHalf =
  BishopProps.≤-trans
    (BishopProps.≤-respʳ-≃
      (BishopProps.∣x*y∣≃∣x∣*∣y∣ x x)
      (BishopProps.x≤∣x∣ {x = square x}))
    (HalfBall.bishopHalfBallMagnitudeSquareBelowQuarter x insideHalf)

sineCoefficientRecurrence : Set
sineCoefficientRecurrence =
  ∀ {x : BishopReal.ℝ} (k : Nat) →
  BishopReal.∣ x ∣ BishopReal.≤ half BishopReal.⋆ →
  BishopReal._⋆ (inverseFactorialRational (oddExponent (suc k)))
    BishopReal.* BishopReal.∣ BishopReal.pow x (oddExponent (suc k)) ∣
    BishopReal.≤
    (oneTwentyFourth BishopReal.⋆)
    BishopReal.*
    (BishopReal._⋆ (inverseFactorialRational (oddExponent k))
      BishopReal.* BishopReal.∣ BishopReal.pow x (oddExponent k) ∣)

cosineCoefficientRecurrence : Set
cosineCoefficientRecurrence =
  ∀ {x : BishopReal.ℝ} (k : Nat) →
  BishopReal.∣ x ∣ BishopReal.≤ half BishopReal.⋆ →
  BishopReal._⋆ (inverseFactorialRational (evenExponent (suc k)))
    BishopReal.* BishopReal.∣ BishopReal.pow x (evenExponent (suc k)) ∣
    BishopReal.≤
    (oneEighth BishopReal.⋆)
    BishopReal.*
    (BishopReal._⋆ (inverseFactorialRational (evenExponent k))
      BishopReal.* BishopReal.∣ BishopReal.pow x (evenExponent k) ∣)

bishopInverseFactorialEncodingLevel : ProofLevel
bishopInverseFactorialEncodingLevel = machineChecked

bishopOddEvenExponentRecurrenceLevel : ProofLevel
bishopOddEvenExponentRecurrenceLevel = machineChecked

bishopFactorialTwoStepRecurrenceLevel : ProofLevel
bishopFactorialTwoStepRecurrenceLevel = machineChecked

bishopHalfBallSquareLevel : ProofLevel
bishopHalfBallSquareLevel = machineChecked

bishopHalfRadiusCoefficientRecurrenceLevel : ProofLevel
bishopHalfRadiusCoefficientRecurrenceLevel = conditional

bishopHalfRadiusRealEstimatesLevel : ProofLevel
bishopHalfRadiusRealEstimatesLevel = conditional
