module DASHI.Foundations.BishopMachinArctanConstructionExact where

------------------------------------------------------------------------
-- PRIMARY / HISTORICAL SOURCES
--
-- John Machin (1706), classical identity
--
--     pi/4 = 4 atan(1/5) - atan(1/239).
--
-- The historical source has no DOI.  For a modern account see Jonathan M.
-- Borwein and Peter B. Borwein, "Pi and the AGM", Wiley, 1987 (book; no DOI
-- assigned to the original edition).
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022, arXiv:2205.08354.
-- No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- DASHI CONTRIBUTION
--
-- This is the non-postulatory pi foundation requested by the YM/Aristotle
-- convergence.  We construct the two arctangent series as ACTUAL Bishop-real
-- limits.  The concrete terms are exactly
--
--   (-1)^n x^(2n+1)/(2n+1).
--
-- Reciprocal odd denominators decrease, the power gains |x|^2 at each step,
-- and on |x|<=1/2 the term magnitude contracts by at most 1/4.  Murray's
-- concrete ratio test therefore proves convergence; no `atan converges` field
-- is introduced.
--
-- We then define the genuine Bishop real
--
--   machinPi_B = 16 atan_B(1/5) - 4 atan_B(1/239).
--
-- IMPORTANT: this file deliberately does NOT call that real the trigonometric
-- pi by theorem.  The remaining foundation seam is the addition/tangent/branch
-- characterization connecting this constructed real to the existing Bishop
-- sine/cosine series.  The rational tangent arithmetic for that bridge is
-- already proved in BishopMachinRationalTangentAlgebraExact.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_; nonNeg)
import Data.Nat.Base as ℕ
open ℕ using (NonZero; _≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_; proj₂)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _/_; _≤_; _<_)
import Data.Rational.Unnormalised.Properties as ℚP

import ExtraProperties as Extra
import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as HalfBall
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact odd reciprocal coefficients 1/(2n+1).
------------------------------------------------------------------------

oddExponentNonZero : ∀ index → NonZero (Estimates.oddExponent index)
oddExponentNonZero zero = _
oddExponentNonZero (suc index) = _

inverseOddRational : Nat → ℚᵘ
inverseOddRational index = + 1 / Estimates.oddExponent index
  where
  instance
    oddNonZero = oddExponentNonZero index

oddExponentStepGrowth : ∀ index →
  Estimates.oddExponent index ≤ Estimates.oddExponent (suc index)
oddExponentStepGrowth index =
  ℕP.≤-trans
    (ℕP.n≤1+n (Estimates.oddExponent index))
    (ℕP.n≤1+n (suc (Estimates.oddExponent index)))

inverseOddStep : ∀ index →
  inverseOddRational (suc index) ℚ.≤ inverseOddRational index
inverseOddStep index =
  let
    old = Estimates.oddExponent index
    new = Estimates.oddExponent (suc index)
    instance
      oldNonZero : NonZero old
      oldNonZero = oddExponentNonZero index
      newNonZero : NonZero new
      newNonZero = oddExponentNonZero (suc index)
  in
  Extra.q≤r⇒+p/r≤+p/q 1 old new (oddExponentStepGrowth index)

inverseOddNonnegative : ∀ index → ℚ.NonNegative (inverseOddRational index)
inverseOddNonnegative zero = nonNeg
inverseOddNonnegative (suc index) = nonNeg

embeddedInverseOddNonnegative : ∀ index →
  BishopReal.NonNegative (BishopReal._⋆ (inverseOddRational index))
embeddedInverseOddNonnegative index =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.p≤q⇒p⋆≤q⋆
      0ℚᵘ
      (inverseOddRational index)
      (ℚP.nonNegative⁻¹
        (inverseOddRational index)
        ⦃ inverseOddNonnegative index ⦄))

embeddedInverseOddStep : ∀ index →
  BishopReal._≤_
    (BishopReal._⋆ (inverseOddRational (suc index)))
    (BishopReal._⋆ (inverseOddRational index))
embeddedInverseOddStep index =
  BishopProperties.p≤q⇒p⋆≤q⋆
    (inverseOddRational (suc index))
    (inverseOddRational index)
    (inverseOddStep index)

------------------------------------------------------------------------
-- Concrete arctangent terms and magnitude contraction.
------------------------------------------------------------------------

atanMagnitudeTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
atanMagnitudeTerm value index =
  BishopReal._*_
    (BishopReal._⋆ (inverseOddRational index))
    (BishopReal.∣_∣
      (BishopReal.pow value (Estimates.oddExponent index)))

atanSignedTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
atanSignedTerm value index =
  BishopReal._*_
    (Terms.alternatingSign index)
    (BishopReal._*_
      (BishopReal._⋆ (inverseOddRational index))
      (BishopReal.pow value (Estimates.oddExponent index)))

atanMagnitudeNonnegative : ∀ value index →
  BishopReal.NonNegative (atanMagnitudeTerm value index)
atanMagnitudeNonnegative value index =
  BishopProperties.nonNegx,y⇒nonNegx*y
    (embeddedInverseOddNonnegative index)
    (BishopProperties.nonNeg∣x∣
      (BishopReal.pow value (Estimates.oddExponent index)))

open BishopProperties.ℝ-Solver

threeFactorRotate : ∀ first second third →
  BishopReal._≃_
    (BishopReal._*_ first (BishopReal._*_ second third))
    (BishopReal._*_ third (BishopReal._*_ first second))
threeFactorRotate first second third =
  solve 3
    (λ a b c → a ⊗ (b ⊗ c) ⊜ c ⊗ (a ⊗ b))
    BishopProperties.≃-refl
    first second third

atanMagnitudeSuccessorBelowSquare : ∀ value index →
  BishopReal._≤_
    (atanMagnitudeTerm value (suc index))
    (BishopReal._*_
      (HalfBall.bishopMagnitudeSquare value)
      (atanMagnitudeTerm value index))
atanMagnitudeSuccessorBelowSquare value index =
  let
    nextExponent = Estimates.oddExponent (suc index)
    oldExponent = Estimates.oddExponent index

    coefficientNonnegative = embeddedInverseOddNonnegative (suc index)
    powerNonnegative =
      BishopProperties.nonNeg∣x∣ (BishopReal.pow value nextExponent)

    raw :
      BishopReal._≤_
        (BishopReal._*_
          (BishopReal._⋆ (inverseOddRational (suc index)))
          (BishopReal.∣_∣ (BishopReal.pow value nextExponent)))
        (BishopReal._*_
          (BishopReal._⋆ (inverseOddRational index))
          (BishopReal._*_
            (BishopReal.∣_∣ (BishopReal.pow value oldExponent))
            (HalfBall.bishopMagnitudeSquare value)))
    raw =
      BishopProperties.*-mono-≤
        coefficientNonnegative
        powerNonnegative
        (embeddedInverseOddStep index)
        (BishopProperties.≤-reflexive
          (Recurrence.absPowOddSuccessorSplit value index))
  in
  BishopProperties.≤-respʳ-≃
    (threeFactorRotate
      (BishopReal._⋆ (inverseOddRational index))
      (BishopReal.∣_∣ (BishopReal.pow value oldExponent))
      (HalfBall.bishopMagnitudeSquare value))
    raw

atanMagnitudeSuccessorBelowQuarter :
  ∀ value index →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  BishopReal._≤_
    (atanMagnitudeTerm value (suc index))
    (BishopReal._*_
      HalfBall.bishopQuarter
      (atanMagnitudeTerm value index))
atanMagnitudeSuccessorBelowQuarter value index insideHalf =
  BishopProperties.≤-trans
    (atanMagnitudeSuccessorBelowSquare value index)
    (BishopProperties.*-monoʳ-≤-nonNeg
      (HalfBall.bishopHalfBallMagnitudeSquareBelowQuarter value insideHalf)
      (atanMagnitudeNonnegative value index))

------------------------------------------------------------------------
-- |(-1)^n coefficient power| is exactly the magnitude term.
------------------------------------------------------------------------

absOneEquivalentOne :
  BishopReal._≃_ (BishopReal.∣_∣ BishopReal.1ℝ) BishopReal.1ℝ
absOneEquivalentOne =
  BishopProperties.0≤x⇒∣x∣≃x BishopProperties.≤-refl

absMinusOneEquivalentOne :
  BishopReal._≃_
    (BishopReal.∣_∣ (BishopReal.- BishopReal.1ℝ))
    BishopReal.1ℝ
absMinusOneEquivalentOne =
  BishopProperties.≃-trans
    BishopProperties.∣-x∣≃∣x∣
    absOneEquivalentOne

alternatingSignAbsOne : ∀ index →
  BishopReal._≃_
    (BishopReal.∣_∣ (Terms.alternatingSign index))
    BishopReal.1ℝ
alternatingSignAbsOne zero = absOneEquivalentOne
alternatingSignAbsOne (suc index) =
  BishopProperties.≃-trans
    (BishopProperties.∣x*y∣≃∣x∣*∣y∣
      (Terms.alternatingSign index) Terms.bishopMinusOne)
    (BishopProperties.≃-trans
      (BishopProperties.*-cong
        (alternatingSignAbsOne index)
        absMinusOneEquivalentOne)
      (BishopProperties.*-identityˡ BishopReal.1ℝ))

embeddedInverseOddAbs : ∀ index →
  BishopReal._≃_
    (BishopReal.∣_∣ (BishopReal._⋆ (inverseOddRational index)))
    (BishopReal._⋆ (inverseOddRational index))
embeddedInverseOddAbs index =
  BishopProperties.0≤x⇒∣x∣≃x
    (BishopProperties.nonNegx⇒0≤x
      (embeddedInverseOddNonnegative index))

atanSignedAbsIsMagnitude : ∀ value index →
  BishopReal._≃_
    (BishopReal.∣_∣ (atanSignedTerm value index))
    (atanMagnitudeTerm value index)
atanSignedAbsIsMagnitude value index =
  BishopProperties.≃-trans
    (BishopProperties.∣x*y∣≃∣x∣*∣y∣
      (Terms.alternatingSign index)
      (BishopReal._*_
        (BishopReal._⋆ (inverseOddRational index))
        (BishopReal.pow value (Estimates.oddExponent index))))
    (BishopProperties.≃-trans
      (BishopProperties.*-cong
        (alternatingSignAbsOne index)
        (BishopProperties.≃-trans
          (BishopProperties.∣x*y∣≃∣x∣*∣y∣
            (BishopReal._⋆ (inverseOddRational index))
            (BishopReal.pow value (Estimates.oddExponent index)))
          (BishopProperties.*-congʳ
            (embeddedInverseOddAbs index))))
      (BishopProperties.*-identityˡ (atanMagnitudeTerm value index)))

atanSignedSuccessorRatioQuarter :
  ∀ value index →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  BishopReal._≤_
    (BishopReal.∣_∣ (atanSignedTerm value (suc index)))
    (BishopReal._*_
      HalfBall.bishopQuarter
      (BishopReal.∣_∣ (atanSignedTerm value index)))
atanSignedSuccessorRatioQuarter value index insideHalf =
  BishopProperties.≤-respʳ-≃
    (BishopProperties.*-congˡ
      (BishopProperties.≃-symm
        (atanSignedAbsIsMagnitude value index)))
    (BishopProperties.≤-respˡ-≃
      (atanSignedAbsIsMagnitude value (suc index))
      (atanMagnitudeSuccessorBelowQuarter value index insideHalf))

------------------------------------------------------------------------
-- Concrete ratio-test convergence on the half-ball.
------------------------------------------------------------------------

quarterPositive : BishopReal._<_ BishopReal.0ℝ HalfBall.bishopQuarter
quarterPositive =
  BishopProperties.posx⇒0<x
    (BishopProperties.posp⇒posp⋆
      HalfBall.quarter
      (ℚP.positive⁻¹ HalfBall.quarter))

oneBelowFour : suc zero < suc (suc (suc (suc zero)))
oneBelowFour = s≤s (s≤s z≤n)

quarterBelowOneRational : HalfBall.quarter ℚ.< 1ℚᵘ
quarterBelowOneRational =
  Extra.q<r⇒+p/r<+p/q 1 1 4 oneBelowFour

quarterBelowOne : BishopReal._<_ HalfBall.bishopQuarter BishopReal.1ℝ
quarterBelowOne =
  BishopProperties.p<q⇒p⋆<q⋆
    HalfBall.quarter 1ℚᵘ quarterBelowOneRational

atanSeriesConvergent :
  ∀ value →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (atanSignedTerm value))
atanSeriesConvergent value insideHalf =
  BishopSequence.proposition-3-6-1
    (quarterPositive , quarterBelowOne)
    (zero , λ index indexAtLeastOne →
      atanSignedSuccessorRatioQuarter value index insideHalf)

bishopAtanHalfBall :
  (value : BishopReal.ℝ) →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  BishopReal.ℝ
bishopAtanHalfBall value insideHalf =
  BishopSequence.lim (atanSeriesConvergent value insideHalf)

bishopAtanHalfBallConverges :
  ∀ value insideHalf →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (atanSignedTerm value))
    (bishopAtanHalfBall value insideHalf)
bishopAtanHalfBallConverges value insideHalf =
  proj₂ (atanSeriesConvergent value insideHalf)

------------------------------------------------------------------------
-- The two Machin arguments are constructively inside the half-ball.
------------------------------------------------------------------------

oneFifth oneTwoHundredThirtyNinth : ℚᵘ
oneFifth = + 1 / 5
oneTwoHundredThirtyNinth = + 1 / 239

bishopOneFifth bishopOneTwoHundredThirtyNinth : BishopReal.ℝ
bishopOneFifth = BishopReal._⋆ oneFifth
bishopOneTwoHundredThirtyNinth = BishopReal._⋆ oneTwoHundredThirtyNinth

twoBelowFive : suc (suc zero) ≤ 5
twoBelowFive = s≤s (s≤s z≤n)

twoBelowTwoHundredThirtyNine : suc (suc zero) ≤ 239
twoBelowTwoHundredThirtyNine = s≤s (s≤s z≤n)

oneFifthBelowHalfRational : oneFifth ℚ.≤ HalfBall.half
oneFifthBelowHalfRational =
  Extra.q≤r⇒+p/r≤+p/q 1 2 5 twoBelowFive

oneTwoHundredThirtyNinthBelowHalfRational :
  oneTwoHundredThirtyNinth ℚ.≤ HalfBall.half
oneTwoHundredThirtyNinthBelowHalfRational =
  Extra.q≤r⇒+p/r≤+p/q 1 2 239 twoBelowTwoHundredThirtyNine

oneFifthNonnegative : BishopReal.NonNegative bishopOneFifth
oneFifthNonnegative =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.p≤q⇒p⋆≤q⋆
      0ℚᵘ oneFifth (ℚP.nonNegative⁻¹ oneFifth))

oneTwoHundredThirtyNinthNonnegative :
  BishopReal.NonNegative bishopOneTwoHundredThirtyNinth
oneTwoHundredThirtyNinthNonnegative =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.p≤q⇒p⋆≤q⋆
      0ℚᵘ oneTwoHundredThirtyNinth
      (ℚP.nonNegative⁻¹ oneTwoHundredThirtyNinth))

bishopOneFifthInsideHalf :
  BishopReal._≤_ (BishopReal.∣_∣ bishopOneFifth) HalfBall.bishopHalf
bishopOneFifthInsideHalf =
  BishopProperties.≤-respˡ-≃
    (BishopProperties.0≤x⇒∣x∣≃x
      (BishopProperties.nonNegx⇒0≤x oneFifthNonnegative))
    (BishopProperties.p≤q⇒p⋆≤q⋆
      oneFifth HalfBall.half oneFifthBelowHalfRational)

bishopOneTwoHundredThirtyNinthInsideHalf :
  BishopReal._≤_
    (BishopReal.∣_∣ bishopOneTwoHundredThirtyNinth)
    HalfBall.bishopHalf
bishopOneTwoHundredThirtyNinthInsideHalf =
  BishopProperties.≤-respˡ-≃
    (BishopProperties.0≤x⇒∣x∣≃x
      (BishopProperties.nonNegx⇒0≤x
        oneTwoHundredThirtyNinthNonnegative))
    (BishopProperties.p≤q⇒p⋆≤q⋆
      oneTwoHundredThirtyNinth HalfBall.half
      oneTwoHundredThirtyNinthBelowHalfRational)

bishopAtanOneFifth bishopAtanOneTwoHundredThirtyNinth : BishopReal.ℝ
bishopAtanOneFifth =
  bishopAtanHalfBall bishopOneFifth bishopOneFifthInsideHalf
bishopAtanOneTwoHundredThirtyNinth =
  bishopAtanHalfBall
    bishopOneTwoHundredThirtyNinth
    bishopOneTwoHundredThirtyNinthInsideHalf

sixteen four : ℚᵘ
sixteen = + 16 / 1
four = + 4 / 1

bishopMachinPi : BishopReal.ℝ
bishopMachinPi =
  BishopReal._-_
    (BishopReal._*_ (BishopReal._⋆ sixteen) bishopAtanOneFifth)
    (BishopReal._*_
      (BishopReal._⋆ four) bishopAtanOneTwoHundredThirtyNinth)

bishopArctangentConcreteOddCoefficientLevel : ProofLevel
bishopArctangentConcreteOddCoefficientLevel = machineChecked

bishopArctangentRatioConvergenceLevel : ProofLevel
bishopArctangentRatioConvergenceLevel = machineChecked

bishopMachinRealConstructionLevel : ProofLevel
bishopMachinRealConstructionLevel = machineChecked

-- The number now exists as a genuine Bishop real.  What remains is semantic
-- characterization, not construction:
--   * prove sine/cosine addition (or tangent addition with nonzero cosine),
--   * combine with the exact rational Machin tangent algebra,
--   * prove the correct constructive quadrant/branch,
--   * conclude sin_B(machinPi)=0 and cos_B(machinPi)=-1.
bishopMachinTrigCharacterizationLevel : ProofLevel
bishopMachinTrigCharacterizationLevel = conditional
