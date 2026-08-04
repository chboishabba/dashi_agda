module DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact where

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
-- Instantiate the generic alternating-interlacing theorem with the actual
-- signed factorial sine and cosine terms.  On the nonnegative half-ball the
-- concrete successor estimates make the magnitudes decreasing; parity of
-- (-1)^n and nonnegativity of powers identify even terms with +m and odd terms
-- with -m.  The represented Bishop series then supplies the common limit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Rational.Unnormalised as ℚ using (1ℚᵘ)

import ExtraProperties as Extra
import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteFactorialCoefficientDischargeExact as Factorial
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as HalfBall
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfRadiusRatiosExact as Ratios
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Brackets
open import DASHI.Physics.YangMills.CompactLieProofLevel

bishopOneNonnegative : BishopReal.NonNegative BishopReal.1ℝ
bishopOneNonnegative =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.≤-refl)

powNonnegative :
  ∀ {value} →
  BishopReal.NonNegative value →
  ∀ exponent →
  BishopReal.NonNegative (BishopReal.pow value exponent)
powNonnegative valueNonnegative zero = bishopOneNonnegative
powNonnegative valueNonnegative (suc exponent) =
  BishopProperties.nonNegx,y⇒nonNegx*y
    (powNonnegative valueNonnegative exponent)
    valueNonnegative

alternatingSignEven :
  ∀ index →
  BishopReal._≃_
    (Terms.alternatingSign (Alternating.double index))
    BishopReal.1ℝ
alternatingSignEven zero = BishopProperties.≃-refl
alternatingSignEven (suc index) =
  let
    exponent = Alternating.double index
    oldSign = Terms.alternatingSign exponent
  in
  BishopProperties.≃-trans
    (Recurrence.powTwoStep Terms.bishopMinusOne exponent)
    (let open BishopProperties.ℝ-Solver
     in solve 1
        (λ sign → sign ⊗ ((⊝ Κ 1ℚᵘ) ⊗ (⊝ Κ 1ℚᵘ)) ⊜ Κ 1ℚᵘ)
        (alternatingSignEven index)
        oldSign)

alternatingSignOdd :
  ∀ index →
  BishopReal._≃_
    (Terms.alternatingSign (suc (Alternating.double index)))
    (BishopReal.- BishopReal.1ℝ)
alternatingSignOdd index =
  let
    evenSign = Terms.alternatingSign (Alternating.double index)
  in
  let open BishopProperties.ℝ-Solver
  in solve 1
      (λ sign → sign ⊗ (⊝ Κ 1ℚᵘ) ⊜ ⊝ Κ 1ℚᵘ)
      (alternatingSignEven index)
      evenSign

sineSignedEvenIsMagnitude :
  ∀ value →
  BishopReal.NonNegative value →
  ∀ index →
  BishopReal._≃_
    (Terms.sineSignedTerm value (Alternating.double index))
    (Recurrence.sineMagnitudeTerm value (Alternating.double index))
sineSignedEvenIsMagnitude value valueNonnegative index =
  let
    termIndex = Alternating.double index
    coefficient = BishopReal._⋆
      (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.inverseFactorialRational
        (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.oddExponent termIndex))
    power = BishopReal.pow value
      (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.oddExponent termIndex)
    powerNonnegativeAtIndex =
      powNonnegative valueNonnegative
        (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.oddExponent termIndex)
  in
  BishopProperties.≃-trans
    (BishopProperties.*-cong
      (alternatingSignEven index)
      (BishopProperties.*-congˡ
        (BishopProperties.≃-symm
          (BishopProperties.nonNegx⇒∣x∣≃x
            powerNonnegativeAtIndex))))
    (BishopProperties.*-identityˡ
      (BishopReal._*_ coefficient (BishopReal.∣_∣ power)))

sineSignedOddIsNegativeMagnitude :
  ∀ value →
  BishopReal.NonNegative value →
  ∀ index →
  BishopReal._≃_
    (Terms.sineSignedTerm value (suc (Alternating.double index)))
    (BishopReal.-
      (Recurrence.sineMagnitudeTerm value
        (suc (Alternating.double index))))
sineSignedOddIsNegativeMagnitude value valueNonnegative index =
  let
    termIndex = suc (Alternating.double index)
    power = BishopReal.pow value
      (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.oddExponent termIndex)
    powerNonnegativeAtIndex =
      powNonnegative valueNonnegative
        (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.oddExponent termIndex)
  in
  BishopProperties.≃-trans
    (BishopProperties.*-cong
      (alternatingSignOdd index)
      (BishopProperties.*-congˡ
        (BishopProperties.≃-symm
          (BishopProperties.nonNegx⇒∣x∣≃x
            powerNonnegativeAtIndex))))
    (let open BishopProperties.ℝ-Solver
     in solve 1
        (λ magnitude → (⊝ Κ 1ℚᵘ) ⊗ magnitude ⊜ ⊝ magnitude)
        BishopProperties.≃-refl
        (Recurrence.sineMagnitudeTerm value termIndex))

cosineSignedEvenIsMagnitude :
  ∀ value →
  BishopReal.NonNegative value →
  ∀ index →
  BishopReal._≃_
    (Terms.cosineSignedTerm value (Alternating.double index))
    (Recurrence.cosineMagnitudeTerm value (Alternating.double index))
cosineSignedEvenIsMagnitude value valueNonnegative index =
  let
    termIndex = Alternating.double index
    coefficient = BishopReal._⋆
      (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.inverseFactorialRational
        (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.evenExponent termIndex))
    power = BishopReal.pow value
      (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.evenExponent termIndex)
    powerNonnegativeAtIndex =
      powNonnegative valueNonnegative
        (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.evenExponent termIndex)
  in
  BishopProperties.≃-trans
    (BishopProperties.*-cong
      (alternatingSignEven index)
      (BishopProperties.*-congˡ
        (BishopProperties.≃-symm
          (BishopProperties.nonNegx⇒∣x∣≃x
            powerNonnegativeAtIndex))))
    (BishopProperties.*-identityˡ
      (BishopReal._*_ coefficient (BishopReal.∣_∣ power)))

cosineSignedOddIsNegativeMagnitude :
  ∀ value →
  BishopReal.NonNegative value →
  ∀ index →
  BishopReal._≃_
    (Terms.cosineSignedTerm value (suc (Alternating.double index)))
    (BishopReal.-
      (Recurrence.cosineMagnitudeTerm value
        (suc (Alternating.double index))))
cosineSignedOddIsNegativeMagnitude value valueNonnegative index =
  let
    termIndex = suc (Alternating.double index)
    power = BishopReal.pow value
      (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.evenExponent termIndex)
    powerNonnegativeAtIndex =
      powNonnegative valueNonnegative
        (DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.evenExponent termIndex)
  in
  BishopProperties.≃-trans
    (BishopProperties.*-cong
      (alternatingSignOdd index)
      (BishopProperties.*-congˡ
        (BishopProperties.≃-symm
          (BishopProperties.nonNegx⇒∣x∣≃x
            powerNonnegativeAtIndex))))
    (let open BishopProperties.ℝ-Solver
     in solve 1
        (λ magnitude → (⊝ Κ 1ℚᵘ) ⊗ magnitude ⊜ ⊝ magnitude)
        BishopProperties.≃-refl
        (Recurrence.cosineMagnitudeTerm value termIndex))

oneTwentyFourthBelowOne :
  BishopReal._≤_ Ratios.bishopOneTwentyFourth BishopReal.1ℝ
oneTwentyFourthBelowOne =
  BishopProperties.p≤q⇒p⋆≤q⋆
    Ratios.oneTwentyFourth 1ℚᵘ
    (Extra.q≤r⇒+p/r≤+p/q 1 1 24 (s≤s z≤n))

oneEighthBelowOne :
  BishopReal._≤_ Ratios.bishopOneEighth BishopReal.1ℝ
oneEighthBelowOne =
  BishopProperties.p≤q⇒p⋆≤q⋆
    Ratios.oneEighth 1ℚᵘ
    (Extra.q≤r⇒+p/r≤+p/q 1 1 8 (s≤s z≤n))

sineMagnitudeDecreasing :
  ∀ value →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  ∀ index →
  BishopReal._≤_
    (Recurrence.sineMagnitudeTerm value (suc index))
    (Recurrence.sineMagnitudeTerm value index)
sineMagnitudeDecreasing value insideHalf index =
  BishopProperties.≤-trans
    (Recurrence.sineMagnitudeTermRecurrence
      Factorial.concreteFactorialCoefficientStepBounds
      value index insideHalf)
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.*-identityˡ
        (Recurrence.sineMagnitudeTerm value index))
      (BishopProperties.*-monoʳ-≤-nonNeg
        oneTwentyFourthBelowOne
        (Recurrence.sineMagnitudeTermNonnegative value index)))

cosineMagnitudeDecreasing :
  ∀ value →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  ∀ index →
  BishopReal._≤_
    (Recurrence.cosineMagnitudeTerm value (suc index))
    (Recurrence.cosineMagnitudeTerm value index)
cosineMagnitudeDecreasing value insideHalf index =
  BishopProperties.≤-trans
    (Recurrence.cosineMagnitudeTermRecurrence
      Factorial.concreteFactorialCoefficientStepBounds
      value index insideHalf)
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.*-identityˡ
        (Recurrence.cosineMagnitudeTerm value index))
      (BishopProperties.*-monoʳ-≤-nonNeg
        oneEighthBelowOne
        (Recurrence.cosineMagnitudeTermNonnegative value index)))

record ConcreteHalfBallSeriesInputs
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set₁ where
  field
    termIdentification :
      Terms.ConcreteSineCosineTermIdentification dataSet

    valueNonnegative : BishopReal.NonNegative value

    insideHalf :
      BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf

open ConcreteHalfBallSeriesInputs public

sineAlternatingSeriesData :
  ∀ {dataSet value} →
  ConcreteHalfBallSeriesInputs dataSet value →
  Alternating.AlternatingDecreasingSeriesData
sineAlternatingSeriesData {dataSet} {value} inputs = record
  { term = Elementary.sineTerm dataSet value
  ; magnitude = Recurrence.sineMagnitudeTerm value
  ; representedLimit = Elementary.bishopSin dataSet value
  ; magnitudeNonnegative =
      Recurrence.sineMagnitudeTermNonnegative value
  ; magnitudeDecreasing =
      sineMagnitudeDecreasing value (insideHalf inputs)
  ; evenTermIsPositiveMagnitude = λ index →
      BishopProperties.≃-trans
        (Terms.sineTermIsConcrete
          (termIdentification inputs) value (Alternating.double index))
        (sineSignedEvenIsMagnitude value
          (valueNonnegative inputs) index)
  ; oddTermIsNegativeMagnitude = λ index →
      BishopProperties.≃-trans
        (Terms.sineTermIsConcrete
          (termIdentification inputs) value
          (suc (Alternating.double index)))
        (sineSignedOddIsNegativeMagnitude value
          (valueNonnegative inputs) index)
  ; seriesConvergesToRepresentedLimit =
      Elementary.bishopSinConvergence dataSet value
  }

cosineAlternatingSeriesData :
  ∀ {dataSet value} →
  ConcreteHalfBallSeriesInputs dataSet value →
  Alternating.AlternatingDecreasingSeriesData
cosineAlternatingSeriesData {dataSet} {value} inputs = record
  { term = Elementary.cosineTerm dataSet value
  ; magnitude = Recurrence.cosineMagnitudeTerm value
  ; representedLimit = Elementary.bishopCos dataSet value
  ; magnitudeNonnegative =
      Recurrence.cosineMagnitudeTermNonnegative value
  ; magnitudeDecreasing =
      cosineMagnitudeDecreasing value (insideHalf inputs)
  ; evenTermIsPositiveMagnitude = λ index →
      BishopProperties.≃-trans
        (Terms.cosineTermIsConcrete
          (termIdentification inputs) value (Alternating.double index))
        (cosineSignedEvenIsMagnitude value
          (valueNonnegative inputs) index)
  ; oddTermIsNegativeMagnitude = λ index →
      BishopProperties.≃-trans
        (Terms.cosineTermIsConcrete
          (termIdentification inputs) value
          (suc (Alternating.double index)))
        (cosineSignedOddIsNegativeMagnitude value
          (valueNonnegative inputs) index)
  ; seriesConvergesToRepresentedLimit =
      Elementary.bishopCosConvergence dataSet value
  }

concreteSineCosineInterlacing :
  ∀ {dataSet value} →
  ConcreteHalfBallSeriesInputs dataSet value →
  Brackets.BishopSineCosineInterlacingData
concreteSineCosineInterlacing inputs = record
  { sineInterlacing =
      Alternating.alternatingInterlacingData
        (sineAlternatingSeriesData inputs)
  ; cosineInterlacing =
      Alternating.alternatingInterlacingData
        (cosineAlternatingSeriesData inputs)
  }

bishopConcreteMagnitudeDecreaseLevel : ProofLevel
bishopConcreteMagnitudeDecreaseLevel = machineChecked

bishopConcreteSineCosineInterlacingLevel : ProofLevel
bishopConcreteSineCosineInterlacingLevel = machineChecked
