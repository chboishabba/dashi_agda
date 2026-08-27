module DASHI.Physics.Closure.NSTriadKNLowMinoritySelfPhaseNormalFormGapRound109Exact where

------------------------------------------------------------------------
-- ROUND109 / LOW-MINORITY SELF-PHASE NORMAL-FORM GAP GAIN
--
-- Round106 already proves for the literal low-minority k geometry
--
--   c_k <= 2 g^2 S,
--
-- where c_k = 2 k (q-p), S=k^2+p^2+q^2 and k <= g p.
--
-- The signed phase normal form uses the static weight eta defined by
--
--   c_k = eta S.
--
-- Since S>0 on a nonzero physical triad, cancellation gives exactly
--
--   eta <= 2 g^2.
--
-- The literal self k-leg phase forcing is the signed majority difference
-- multiplied by the nonnegative projected-cross square mass.  Therefore the
-- adverse-oriented self normal-form contribution retains the SAME two gap
-- powers before any absolute value or network summation:
--
--   eta (q-p) M <= 2 g^2 (q-p) M,       M >= 0.
--
-- A further use of q-p <= k <= g p gives the displayed three-gap shell form
--
--   eta (q-p) M <= 2 g^3 p M.
--
-- This closes the far-separated LOW-MINORITY self-channel geometry only.  It
-- does not close the complete self-phase payment: high-minority and comparable
-- cells remain separate physical leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; NonNegative; Positive; nonNegative; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLowMinorityLiteralGapPhaseWeightRound106Exact as Low
import DASHI.Physics.Closure.NSTriadKNHeterochiralGapRelativeDampingRound106Exact as Gap
import DASHI.Physics.Closure.NSTriadKNHeterochiralReverseTriangleRound105Exact as Triangle

record LowMinoritySelfNormalFormDatum : Set where
  constructor low-minority-self-normal-form-datum
  field
    geometry : Low.LowMinorityKGapDatum
    normalFormWeight : ℚ
    dampingScalePositive : 0ℚ < Low.phaseDampingScale geometry
    normalFormFactorization :
      Low.lowMinorityKCoefficient geometry
      ≡ normalFormWeight * Low.phaseDampingScale geometry

open LowMinoritySelfNormalFormDatum public

twoGapSquared : LowMinoritySelfNormalFormDatum → ℚ
twoGapSquared D = Gap.two * (Low.gap (geometry D) * Low.gap (geometry D))

majorityDifference : LowMinoritySelfNormalFormDatum → ℚ
majorityDifference D =
  Triangle.radiusQ (Low.radii (geometry D))
  - Triangle.radiusP (Low.radii (geometry D))

lowMinorityNormalFormWeightBelowTwoGapSquared :
  (D : LowMinoritySelfNormalFormDatum) →
  normalFormWeight D ≤ twoGapSquared D
lowMinorityNormalFormWeightBelowTwoGapSquared D =
  let
    S = Low.phaseDampingScale (geometry D)
    eta = normalFormWeight D
    upper = twoGapSquared D

    coefficientBound :
      Low.lowMinorityKCoefficient (geometry D) ≤ upper * S
    coefficientBound = Low.literalLowMinorityCoefficientHasSquaredGap (geometry D)

    factorized : eta * S ≤ upper * S
    factorized =
      subst
        (λ left → left ≤ upper * S)
        (normalFormFactorization D)
        coefficientBound

    instance sPositive : Positive S
    sPositive = positive (dampingScalePositive D)
  in
  ℚP.*-cancelʳ-≤-pos S factorized

majorityDifferenceNonnegative :
  (D : LowMinoritySelfNormalFormDatum) →
  0ℚ ≤ majorityDifference D
majorityDifferenceNonnegative D =
  Low.majorityDifferenceNonnegative (geometry D)

selfSquareMassContribution :
  LowMinoritySelfNormalFormDatum → ℚ → ℚ
selfSquareMassContribution D squareMass =
  normalFormWeight D * majorityDifference D * squareMass

lowMinoritySelfNormalFormCarriesTwoGapPowers :
  (D : LowMinoritySelfNormalFormDatum) →
  (squareMass : ℚ) →
  0ℚ ≤ squareMass →
  selfSquareMassContribution D squareMass
  ≤ twoGapSquared D * majorityDifference D * squareMass
lowMinoritySelfNormalFormCarriesTwoGapPowers D squareMass squareMassNN =
  let
    differenceNN = majorityDifferenceNonnegative D
    first :
      normalFormWeight D * majorityDifference D
      ≤ twoGapSquared D * majorityDifference D
    first =
      let instance differenceNNI = nonNegative differenceNN
      in ℚP.*-monoʳ-≤-nonNeg
          (majorityDifference D)
          (lowMinorityNormalFormWeightBelowTwoGapSquared D)
  in
  let instance squareMassNNI = nonNegative squareMassNN
  in ℚP.*-monoʳ-≤-nonNeg squareMass first

majorityDifferenceBelowGapHigh :
  (D : LowMinoritySelfNormalFormDatum) →
  majorityDifference D
  ≤ Low.gap (geometry D) * Triangle.radiusP (Low.radii (geometry D))
majorityDifferenceBelowGapHigh D =
  let
    G = geometry D
    diffBelowLow :
      majorityDifference D ≤ Triangle.radiusK (Low.radii G)
    diffBelowLow = Triangle.qMinusPBelowK (Low.radii G)
  in
  ℚP.≤-trans diffBelowLow (Low.lowBelowGapHighP G)

lowMinoritySelfNormalFormCarriesThreeGapShellPowers :
  (D : LowMinoritySelfNormalFormDatum) →
  (squareMass : ℚ) →
  0ℚ ≤ squareMass →
  selfSquareMassContribution D squareMass
  ≤
  (Gap.two *
    ((Low.gap (geometry D) * Low.gap (geometry D)) * Low.gap (geometry D)))
  * Triangle.radiusP (Low.radii (geometry D))
  * squareMass
lowMinoritySelfNormalFormCarriesThreeGapShellPowers D squareMass squareMassNN =
  let
    gap = Low.gap (geometry D)
    high = Triangle.radiusP (Low.radii (geometry D))
    difference = majorityDifference D
    gapNN = Low.gapNonnegative (geometry D)
    twoGap2 = twoGapSquared D

    twoGap2NN : 0ℚ ≤ twoGap2
    twoGap2NN =
      let
        instance twoNNI = nonNegative Gap.twoNonnegative
        gapNNI = nonNegative gapNN
        gap2NNI = ℚP.nonNeg*nonNeg⇒nonNeg gap gap
      in ℚP.nonNegative⁻¹ twoGap2

    differenceStep :
      twoGap2 * difference ≤ twoGap2 * (gap * high)
    differenceStep =
      let instance coefficientNNI = nonNegative twoGap2NN
      in ℚP.*-monoˡ-≤-nonNeg twoGap2 (majorityDifferenceBelowGapHigh D)

    shellMeaning :
      twoGap2 * (gap * high)
      ≡
      (Gap.two * ((gap * gap) * gap)) * high
    shellMeaning = solve (gap ∷ high ∷ [])

    withMass :
      (twoGap2 * difference) * squareMass
      ≤ ((Gap.two * ((gap * gap) * gap)) * high) * squareMass
    withMass =
      let instance massNNI = nonNegative squareMassNN
      in ℚP.*-monoʳ-≤-nonNeg squareMass
        (subst
          (λ upper → twoGap2 * difference ≤ upper)
          shellMeaning differenceStep)
  in
  ℚP.≤-trans
    (lowMinoritySelfNormalFormCarriesTwoGapPowers D squareMass squareMassNN)
    withMass

round109LowMinoritySelfNormalFormWeightCarriesTwoGapPowers : Bool
round109LowMinoritySelfNormalFormWeightCarriesTwoGapPowers = true

round109LowMinoritySelfPhaseCarriesThreeGapShellPowers : Bool
round109LowMinoritySelfPhaseCarriesThreeGapShellPowers = true

round109CompleteSelfPhasePaymentClosed : Bool
round109CompleteSelfPhasePaymentClosed = false

round109LowMinoritySelfNormalFormWeightCarriesTwoGapPowersIsTrue :
  round109LowMinoritySelfNormalFormWeightCarriesTwoGapPowers ≡ true
round109LowMinoritySelfNormalFormWeightCarriesTwoGapPowersIsTrue = refl

round109LowMinoritySelfPhaseCarriesThreeGapShellPowersIsTrue :
  round109LowMinoritySelfPhaseCarriesThreeGapShellPowers ≡ true
round109LowMinoritySelfPhaseCarriesThreeGapShellPowersIsTrue = refl

round109CompleteSelfPhasePaymentClosedIsFalse :
  round109CompleteSelfPhasePaymentClosed ≡ false
round109CompleteSelfPhasePaymentClosedIsFalse = refl
