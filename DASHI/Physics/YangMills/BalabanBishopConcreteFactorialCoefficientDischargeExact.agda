module DASHI.Physics.YangMills.BalabanBishopConcreteFactorialCoefficientDischargeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
-- Discharge the two reciprocal-factorial leaves left by round nine.  The proof
-- is deliberately split into natural denominator growth, unnormalised-rational
-- antitonicity of positive reciprocals, Bishop-real embedding, and finally the
-- exact sine/cosine magnitude-term inequalities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as ℤ using (ℤ; +_)
open import Data.Nat.Base as ℕ using
  (NonZero; _≤_; _*_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; _/_; _*_; _≤_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import ExtraProperties as Extra
import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfRadiusRatiosExact as Ratios
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Small natural-number lower bounds for the two factorial step factors.
------------------------------------------------------------------------

oddExponentPositive :
  ∀ index → suc zero ≤ Estimates.oddExponent index
oddExponentPositive zero = s≤s z≤n
oddExponentPositive (suc index) = s≤s z≤n

twoBelowSuccessorOddExponent :
  ∀ index → suc (suc zero) ≤ suc (Estimates.oddExponent index)
twoBelowSuccessorOddExponent index =
  s≤s (oddExponentPositive index)

threeBelowDoubleSuccessorOddExponent :
  ∀ index →
  suc (suc (suc zero)) ≤ suc (suc (Estimates.oddExponent index))
threeBelowDoubleSuccessorOddExponent index =
  s≤s (twoBelowSuccessorOddExponent index)

sixBelowOddFactorialStepFactor :
  ∀ index →
  suc (suc (suc (suc (suc (suc zero)))))
  ≤ suc (suc (Estimates.oddExponent index))
      * suc (Estimates.oddExponent index)
sixBelowOddFactorialStepFactor index =
  ℕP.*-mono-≤
    (threeBelowDoubleSuccessorOddExponent index)
    (twoBelowSuccessorOddExponent index)

twoBelowEvenFactorialStepFactor :
  ∀ index →
  suc (suc zero)
  ≤ suc (suc (Estimates.evenExponent index))
      * suc (Estimates.evenExponent index)
twoBelowEvenFactorialStepFactor index =
  ℕP.*-mono-≤
    (s≤s (s≤s z≤n))
    (s≤s z≤n)

six : Nat
six = suc (suc (suc (suc (suc (suc zero)))))

two : Nat
two = suc (suc zero)

oddFactorialDenominatorGrowth :
  ∀ index →
  six * Estimates.factorial (Estimates.oddExponent index)
  ≤ Estimates.factorial (Estimates.oddExponent (suc index))
oddFactorialDenominatorGrowth index =
  let
    oldExponent = Estimates.oddExponent index
    oldFactorial = Estimates.factorial oldExponent
    leftFactor = suc (suc oldExponent)
    rightFactor = suc oldExponent

    multiplied :
      six * oldFactorial
      ≤ (leftFactor * rightFactor) * oldFactorial
    multiplied =
      ℕP.*-monoʳ-≤ oldFactorial
        (sixBelowOddFactorialStepFactor index)

    associated :
      six * oldFactorial
      ≤ leftFactor * (rightFactor * oldFactorial)
    associated =
      subst
        (λ value → six * oldFactorial ≤ value)
        (ℕP.*-assoc leftFactor rightFactor oldFactorial)
        multiplied
  in
  subst
    (λ value → six * oldFactorial ≤ value)
    (sym (Estimates.oddFactorialSuccessor index))
    associated

evenFactorialDenominatorGrowth :
  ∀ index →
  two * Estimates.factorial (Estimates.evenExponent index)
  ≤ Estimates.factorial (Estimates.evenExponent (suc index))
evenFactorialDenominatorGrowth index =
  let
    oldExponent = Estimates.evenExponent index
    oldFactorial = Estimates.factorial oldExponent
    leftFactor = suc (suc oldExponent)
    rightFactor = suc oldExponent

    multiplied :
      two * oldFactorial
      ≤ (leftFactor * rightFactor) * oldFactorial
    multiplied =
      ℕP.*-monoʳ-≤ oldFactorial
        (twoBelowEvenFactorialStepFactor index)

    associated :
      two * oldFactorial
      ≤ leftFactor * (rightFactor * oldFactorial)
    associated =
      subst
        (λ value → two * oldFactorial ≤ value)
        (ℕP.*-assoc leftFactor rightFactor oldFactorial)
        multiplied
  in
  subst
    (λ value → two * oldFactorial ≤ value)
    (sym (Estimates.evenFactorialSuccessor index))
    associated

------------------------------------------------------------------------
-- Exact positive-fraction multiplication and reciprocal antitonicity.
------------------------------------------------------------------------

positiveUnitFractionProduct :
  (leftDenominator rightDenominator : Nat)
  .{{_ : NonZero leftDenominator}}
  .{{_ : NonZero rightDenominator}}
  .{{_ : NonZero (leftDenominator * rightDenominator)}} →
  ((+ 1 / leftDenominator) ℚ.* (+ 1 / rightDenominator))
  ≡ (+ 1 / (leftDenominator * rightDenominator))
positiveUnitFractionProduct (suc left) (suc right) = refl

oddInverseFactorialStep :
  ∀ index →
  Estimates.inverseFactorialRational
      (Estimates.oddExponent (suc index))
  ℚ.≤
  Ratios.oneSixth ℚ.*
    Estimates.inverseFactorialRational
      (Estimates.oddExponent index)
oddInverseFactorialStep index =
  let
    oldExponent = Estimates.oddExponent index
    newExponent = Estimates.oddExponent (suc index)
    oldFactorial = Estimates.factorial oldExponent
    newFactorial = Estimates.factorial newExponent

    instance
      oldFactorialNonZero : NonZero oldFactorial
      oldFactorialNonZero = ℕ.≢-nonZero (ℕP._!≢0 oldExponent)

      newFactorialNonZero : NonZero newFactorial
      newFactorialNonZero = ℕ.≢-nonZero (ℕP._!≢0 newExponent)

      sixNonZero : NonZero six
      sixNonZero = _

      sixTimesOldNonZero : NonZero (six * oldFactorial)
      sixTimesOldNonZero =
        ℕ.≢-nonZero
          (Extra.m,n≢0⇒mn≢0 six oldFactorial)

    reciprocalBound :
      (+ 1 / newFactorial) ℚ.≤ (+ 1 / (six * oldFactorial))
    reciprocalBound =
      Extra.q≤r⇒+p/r≤+p/q
        1
        (six * oldFactorial)
        newFactorial
        (oddFactorialDenominatorGrowth index)

    productEquality :
      Ratios.oneSixth ℚ.* (+ 1 / oldFactorial)
      ≡ (+ 1 / (six * oldFactorial))
    productEquality =
      positiveUnitFractionProduct six oldFactorial
  in
  ℚP.≤-respʳ-≃
    (ℚP.≃-sym (ℚP.≃-reflexive productEquality))
    reciprocalBound

evenInverseFactorialStep :
  ∀ index →
  Estimates.inverseFactorialRational
      (Estimates.evenExponent (suc index))
  ℚ.≤
  Ratios.oneHalf ℚ.*
    Estimates.inverseFactorialRational
      (Estimates.evenExponent index)
evenInverseFactorialStep index =
  let
    oldExponent = Estimates.evenExponent index
    newExponent = Estimates.evenExponent (suc index)
    oldFactorial = Estimates.factorial oldExponent
    newFactorial = Estimates.factorial newExponent

    instance
      oldFactorialNonZero : NonZero oldFactorial
      oldFactorialNonZero = ℕ.≢-nonZero (ℕP._!≢0 oldExponent)

      newFactorialNonZero : NonZero newFactorial
      newFactorialNonZero = ℕ.≢-nonZero (ℕP._!≢0 newExponent)

      twoNonZero : NonZero two
      twoNonZero = _

      twoTimesOldNonZero : NonZero (two * oldFactorial)
      twoTimesOldNonZero =
        ℕ.≢-nonZero
          (Extra.m,n≢0⇒mn≢0 two oldFactorial)

    reciprocalBound :
      (+ 1 / newFactorial) ℚ.≤ (+ 1 / (two * oldFactorial))
    reciprocalBound =
      Extra.q≤r⇒+p/r≤+p/q
        1
        (two * oldFactorial)
        newFactorial
        (evenFactorialDenominatorGrowth index)

    productEquality :
      Ratios.oneHalf ℚ.* (+ 1 / oldFactorial)
      ≡ (+ 1 / (two * oldFactorial))
    productEquality =
      positiveUnitFractionProduct two oldFactorial
  in
  ℚP.≤-respʳ-≃
    (ℚP.≃-sym (ℚP.≃-reflexive productEquality))
    reciprocalBound

embeddedOddInverseFactorialStep :
  ∀ index →
  BishopReal._≤_
    (BishopReal._⋆
      (Estimates.inverseFactorialRational
        (Estimates.oddExponent (suc index))))
    (BishopReal._*_
      Ratios.bishopOneSixth
      (BishopReal._⋆
        (Estimates.inverseFactorialRational
          (Estimates.oddExponent index))))
embeddedOddInverseFactorialStep index =
  BishopProperties.≤-respʳ-≃
    (BishopProperties.⋆-distrib-*
      Ratios.oneSixth
      (Estimates.inverseFactorialRational
        (Estimates.oddExponent index)))
    (BishopProperties.p≤q⇒p⋆≤q⋆
      (Estimates.inverseFactorialRational
        (Estimates.oddExponent (suc index)))
      (Ratios.oneSixth ℚ.*
        Estimates.inverseFactorialRational
          (Estimates.oddExponent index))
      (oddInverseFactorialStep index))

embeddedEvenInverseFactorialStep :
  ∀ index →
  BishopReal._≤_
    (BishopReal._⋆
      (Estimates.inverseFactorialRational
        (Estimates.evenExponent (suc index))))
    (BishopReal._*_
      Ratios.bishopOneHalf
      (BishopReal._⋆
        (Estimates.inverseFactorialRational
          (Estimates.evenExponent index))))
embeddedEvenInverseFactorialStep index =
  BishopProperties.≤-respʳ-≃
    (BishopProperties.⋆-distrib-*
      Ratios.oneHalf
      (Estimates.inverseFactorialRational
        (Estimates.evenExponent index)))
    (BishopProperties.p≤q⇒p⋆≤q⋆
      (Estimates.inverseFactorialRational
        (Estimates.evenExponent (suc index)))
      (Ratios.oneHalf ℚ.*
        Estimates.inverseFactorialRational
          (Estimates.evenExponent index))
      (evenInverseFactorialStep index))

------------------------------------------------------------------------
-- Reassociate the two monotone products into the exact physical ratios.
------------------------------------------------------------------------

open BishopProperties.ℝ-Solver

fourFactorReassociation :
  ∀ first second third fourth →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_ first second)
      (BishopReal._*_ third fourth))
    (BishopReal._*_
      (BishopReal._*_ fourth first)
      (BishopReal._*_ second third))
fourFactorReassociation first second third fourth =
  solve 4
    (λ a b c d →
      (a ⊗ b) ⊗ (c ⊗ d) ⊜ (d ⊗ a) ⊗ (b ⊗ c))
    BishopProperties.≃-refl
    first second third fourth

sineSuccessorBelowCoarseRatio :
  ∀ value index →
  BishopReal._≤_
    (Recurrence.sineMagnitudeTerm value (suc index))
    (BishopReal._*_
      (Ratios.bishopSineSuccessiveMagnitudeRatio value)
      (Recurrence.sineMagnitudeTerm value index))
sineSuccessorBelowCoarseRatio value index =
  let
    nextExponent = Estimates.oddExponent (suc index)
    oldExponent = Estimates.oddExponent index

    coefficientNonnegative =
      Recurrence.embeddedInverseFactorialNonnegative nextExponent

    powerNonnegative =
      BishopProperties.nonNeg∣x∣
        (BishopReal.pow value nextExponent)

    monotoneProduct =
      BishopProperties.*-mono-≤
        coefficientNonnegative
        powerNonnegative
        (embeddedOddInverseFactorialStep index)
        (BishopProperties.≤-reflexive
          (Recurrence.absPowOddSuccessorSplit value index))
  in
  BishopProperties.≤-respʳ-≃
    (fourFactorReassociation
      Ratios.bishopOneSixth
      (BishopReal._⋆
        (Estimates.inverseFactorialRational oldExponent))
      (BishopReal.∣_∣ (BishopReal.pow value oldExponent))
      (BishopReal._*_
        (BishopReal.∣_∣ value)
        (BishopReal.∣_∣ value)))
    monotoneProduct

cosineSuccessorBelowCoarseRatio :
  ∀ value index →
  BishopReal._≤_
    (Recurrence.cosineMagnitudeTerm value (suc index))
    (BishopReal._*_
      (Ratios.bishopCosineSuccessiveMagnitudeRatio value)
      (Recurrence.cosineMagnitudeTerm value index))
cosineSuccessorBelowCoarseRatio value index =
  let
    nextExponent = Estimates.evenExponent (suc index)
    oldExponent = Estimates.evenExponent index

    coefficientNonnegative =
      Recurrence.embeddedInverseFactorialNonnegative nextExponent

    powerNonnegative =
      BishopProperties.nonNeg∣x∣
        (BishopReal.pow value nextExponent)

    monotoneProduct =
      BishopProperties.*-mono-≤
        coefficientNonnegative
        powerNonnegative
        (embeddedEvenInverseFactorialStep index)
        (BishopProperties.≤-reflexive
          (Recurrence.absPowEvenSuccessorSplit value index))
  in
  BishopProperties.≤-respʳ-≃
    (fourFactorReassociation
      Ratios.bishopOneHalf
      (BishopReal._⋆
        (Estimates.inverseFactorialRational oldExponent))
      (BishopReal.∣_∣ (BishopReal.pow value oldExponent))
      (BishopReal._*_
        (BishopReal.∣_∣ value)
        (BishopReal.∣_∣ value)))
    monotoneProduct

concreteFactorialCoefficientStepBounds :
  Recurrence.ConcreteFactorialCoefficientStepBounds
concreteFactorialCoefficientStepBounds = record
  { sineSuccessorBelowCoarseRatio =
      sineSuccessorBelowCoarseRatio
  ; cosineSuccessorBelowCoarseRatio =
      cosineSuccessorBelowCoarseRatio
  }

bishopNaturalFactorialGrowthLevel : ProofLevel
bishopNaturalFactorialGrowthLevel = machineChecked

bishopReciprocalFactorialStepLevel : ProofLevel
bishopReciprocalFactorialStepLevel = machineChecked

bishopConcreteFactorialCoefficientStepDischargeLevel : ProofLevel
bishopConcreteFactorialCoefficientStepDischargeLevel = machineChecked
