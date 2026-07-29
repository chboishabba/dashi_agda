module DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Agda standard-library contributors; DASHI repository contributors.
-- Title: "Exact rational finite geometric envelope for output relocation".
-- Venue/year: Agda standard library; DASHI formal development, 2026.
-- DOI: not applicable; the finite geometric identity is classical and this
-- repository-specialised proof has no DOI.
-- Uses: exact reduced rationals, the rational commutative-ring solver, and
-- positivity/cancellation in the rational ordered field.
-- Relationship: proves uniformly in both finite cutoffs that
--
--   sum_{j=0}^J (1/4)^j <= 4/3,
--   sum_{d=0}^D (1/32)^d <= 32/31,
--
-- and hence that their rectangular product is at most 128/93.  This closes
-- finite geometric summation itself.  It does not identify a non-integral
-- H^s shell factor with either rational envelope; that comparison remains a
-- separate two-lemma bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; subst; sym)
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

pow : ℚ → Nat → ℚ
pow ratio zero = 1ℚ
pow ratio (suc exponent) = ratio * pow ratio exponent

-- The ordinary inclusive prefix sum
--
--   partialSum r N = 1 + r + ... + r^N.
partialSum : ℚ → Nat → ℚ
partialSum ratio zero = 1ℚ
partialSum ratio (suc cutoff) =
  pow ratio (suc cutoff) + partialSum ratio cutoff

geometricIdentity : ∀ ratio cutoff →
  (1ℚ - ratio) * partialSum ratio cutoff
  ≡ 1ℚ - pow ratio (suc cutoff)
geometricIdentity ratio zero = solve (ratio ∷ [])
geometricIdentity ratio (suc cutoff) =
  begin
    (1ℚ - ratio) * partialSum ratio (suc cutoff)
  ≡⟨ solve
       (ratio ∷ pow ratio (suc cutoff)
        ∷ partialSum ratio cutoff ∷ []) ⟩
    (1ℚ - ratio) * pow ratio (suc cutoff)
      + (1ℚ - ratio) * partialSum ratio cutoff
  ≡⟨ cong
       (λ value →
         (1ℚ - ratio) * pow ratio (suc cutoff) + value)
       (geometricIdentity ratio cutoff) ⟩
    (1ℚ - ratio) * pow ratio (suc cutoff)
      + (1ℚ - pow ratio (suc cutoff))
  ≡⟨ solve (ratio ∷ pow ratio (suc cutoff) ∷ []) ⟩
    1ℚ - pow ratio (suc (suc cutoff))
  ∎

zeroBelowOne : 0ℚ ≤ 1ℚ
zeroBelowOne = toWitness (0ℚ ≤? 1ℚ)

powNonnegative : ∀ ratio exponent →
  0ℚ ≤ ratio → 0ℚ ≤ pow ratio exponent
powNonnegative ratio zero ratioNonnegative = zeroBelowOne
powNonnegative ratio (suc exponent) ratioNonnegative =
  let
    instance
      ratioIsNonnegative = ℚₚ.nonNegative ratioNonnegative
      restIsNonnegative =
        ℚₚ.nonNegative (powNonnegative ratio exponent ratioNonnegative)
  in
  ℚₚ.nonNegative⁻¹ (ratio * pow ratio exponent)

partialSumNonnegative : ∀ ratio cutoff →
  0ℚ ≤ ratio → 0ℚ ≤ partialSum ratio cutoff
partialSumNonnegative ratio zero ratioNonnegative = zeroBelowOne
partialSumNonnegative ratio (suc cutoff) ratioNonnegative =
  let
    currentPowerNonnegative =
      powNonnegative ratio (suc cutoff) ratioNonnegative
    restNonnegative =
      partialSumNonnegative ratio cutoff ratioNonnegative
    instance
      currentPowerIsNonnegative =
        ℚₚ.nonNegative currentPowerNonnegative
      restIsNonnegative = ℚₚ.nonNegative restNonnegative
      sumIsNonnegative =
        ℚₚ.nonNeg+nonNeg⇒nonNeg
          (pow ratio (suc cutoff)) (partialSum ratio cutoff)
  in
  ℚₚ.nonNegative⁻¹
    (pow ratio (suc cutoff) + partialSum ratio cutoff)

geometricPartialSumBound : ∀ ratio bound cutoff →
  0ℚ ≤ ratio →
  0ℚ < 1ℚ - ratio →
  (1ℚ - ratio) * bound ≡ 1ℚ →
  partialSum ratio cutoff ≤ bound
geometricPartialSumBound ratio bound cutoff
    ratioNonnegative oneMinusRatioPositive boundIdentity =
  let
    tailPowerNonnegative :
      0ℚ ≤ pow ratio (suc cutoff)
    tailPowerNonnegative =
      powNonnegative ratio (suc cutoff) ratioNonnegative

    tailBelowOne :
      1ℚ - pow ratio (suc cutoff) ≤ 1ℚ
    tailBelowOne =
      L2.subtractNonnegativeBelow
        1ℚ (pow ratio (suc cutoff)) tailPowerNonnegative

    scaledBound :
      (1ℚ - ratio) * partialSum ratio cutoff
      ≤ (1ℚ - ratio) * bound
    scaledBound =
      subst
        (λ left → left ≤ (1ℚ - ratio) * bound)
        (sym (geometricIdentity ratio cutoff))
        (subst
          (λ right → 1ℚ - pow ratio (suc cutoff) ≤ right)
          (sym boundIdentity)
          tailBelowOne)

    instance
      oneMinusRatioIsPositive =
        ℚₚ.positive oneMinusRatioPositive
  in
  ℚₚ.*-cancelˡ-≤-pos (1ℚ - ratio) scaledBound

quarter thirtySecond fourThirds thirtyTwoThirtyFirsts
  oneTwentyEightNinetyThirds : ℚ
quarter = Int.+ 1 / 4
thirtySecond = Int.+ 1 / 32
fourThirds = Int.+ 4 / 3
thirtyTwoThirtyFirsts = Int.+ 32 / 31
oneTwentyEightNinetyThirds = Int.+ 128 / 93

quarterNonnegative : 0ℚ ≤ quarter
quarterNonnegative = toWitness (0ℚ ≤? quarter)

thirtySecondNonnegative : 0ℚ ≤ thirtySecond
thirtySecondNonnegative = toWitness (0ℚ ≤? thirtySecond)

oneMinusQuarterPositive : 0ℚ < 1ℚ - quarter
oneMinusQuarterPositive = toWitness (0ℚ <? 1ℚ - quarter)

oneMinusThirtySecondPositive : 0ℚ < 1ℚ - thirtySecond
oneMinusThirtySecondPositive =
  toWitness (0ℚ <? 1ℚ - thirtySecond)

fourThirdsNonnegative : 0ℚ ≤ fourThirds
fourThirdsNonnegative = toWitness (0ℚ ≤? fourThirds)

thirtyTwoThirtyFirstsNonnegative : 0ℚ ≤ thirtyTwoThirtyFirsts
thirtyTwoThirtyFirstsNonnegative =
  toWitness (0ℚ ≤? thirtyTwoThirtyFirsts)

quarterBoundIdentity :
  (1ℚ - quarter) * fourThirds ≡ 1ℚ
quarterBoundIdentity = refl

thirtySecondBoundIdentity :
  (1ℚ - thirtySecond) * thirtyTwoThirtyFirsts ≡ 1ℚ
thirtySecondBoundIdentity = refl

quarterPartialSumBound : ∀ cutoff →
  partialSum quarter cutoff ≤ fourThirds
quarterPartialSumBound cutoff =
  geometricPartialSumBound
    quarter fourThirds cutoff
    quarterNonnegative oneMinusQuarterPositive quarterBoundIdentity

thirtySecondPartialSumBound : ∀ cutoff →
  partialSum thirtySecond cutoff ≤ thirtyTwoThirtyFirsts
thirtySecondPartialSumBound cutoff =
  geometricPartialSumBound
    thirtySecond thirtyTwoThirtyFirsts cutoff
    thirtySecondNonnegative
    oneMinusThirtySecondPositive
    thirtySecondBoundIdentity

rectanglePartialSumBound : ∀ lowCutoff gapCutoff →
  partialSum quarter lowCutoff * partialSum thirtySecond gapCutoff
  ≤ fourThirds * thirtyTwoThirtyFirsts
rectanglePartialSumBound lowCutoff gapCutoff =
  let
    gapSumNonnegative =
      partialSumNonnegative
        thirtySecond gapCutoff thirtySecondNonnegative

    firstStep :
      partialSum quarter lowCutoff * partialSum thirtySecond gapCutoff
      ≤ fourThirds * partialSum thirtySecond gapCutoff
    firstStep =
      let
        instance
          gapSumIsNonnegative = ℚₚ.nonNegative gapSumNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (partialSum thirtySecond gapCutoff)
        (quarterPartialSumBound lowCutoff)

    secondStep :
      fourThirds * partialSum thirtySecond gapCutoff
      ≤ fourThirds * thirtyTwoThirtyFirsts
    secondStep =
      let
        instance
          fourThirdsIsNonnegative =
            ℚₚ.nonNegative fourThirdsNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        fourThirds
        (thirtySecondPartialSumBound gapCutoff)
  in
  ℚₚ.≤-trans firstStep secondStep

productConstantIdentity :
  fourThirds * thirtyTwoThirtyFirsts
  ≡ oneTwentyEightNinetyThirds
productConstantIdentity = refl

rectanglePartialSumBoundExact : ∀ lowCutoff gapCutoff →
  partialSum quarter lowCutoff * partialSum thirtySecond gapCutoff
  ≤ oneTwentyEightNinetyThirds
rectanglePartialSumBoundExact lowCutoff gapCutoff =
  subst
    (λ upper →
      partialSum quarter lowCutoff * partialSum thirtySecond gapCutoff
      ≤ upper)
    productConstantIdentity
    (rectanglePartialSumBound lowCutoff gapCutoff)

rationalFiniteGeometricEnvelopeClosed : Bool
rationalFiniteGeometricEnvelopeClosed = true

quarterUniformPartialSumClosed : Bool
quarterUniformPartialSumClosed = true

thirtySecondUniformPartialSumClosed : Bool
thirtySecondUniformPartialSumClosed = true

rectangularOneTwentyEightOverNinetyThreeClosed : Bool
rectangularOneTwentyEightOverNinetyThreeClosed = true

rationalFiniteGeometricEnvelopeClosedIsTrue :
  rationalFiniteGeometricEnvelopeClosed ≡ true
rationalFiniteGeometricEnvelopeClosedIsTrue = refl

quarterUniformPartialSumClosedIsTrue :
  quarterUniformPartialSumClosed ≡ true
quarterUniformPartialSumClosedIsTrue = refl

thirtySecondUniformPartialSumClosedIsTrue :
  thirtySecondUniformPartialSumClosed ≡ true
thirtySecondUniformPartialSumClosedIsTrue = refl

rectangularOneTwentyEightOverNinetyThreeClosedIsTrue :
  rectangularOneTwentyEightOverNinetyThreeClosed ≡ true
rectangularOneTwentyEightOverNinetyThreeClosedIsTrue = refl
