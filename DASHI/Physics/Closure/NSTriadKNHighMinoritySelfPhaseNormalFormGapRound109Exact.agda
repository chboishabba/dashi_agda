module DASHI.Physics.Closure.NSTriadKNHighMinoritySelfPhaseNormalFormGapRound109Exact where

------------------------------------------------------------------------
-- ROUND109 / HIGH-MINORITY SELF-PHASE NORMAL-FORM GAP GAIN
--
-- Round106 already supplies the exact ordered implication
--
--   c <= 2 L H   and   L <= g H   and   H^2 <= S
--     ==> c <= 2 g S.
--
-- If the signed phase normal-form weight eta satisfies c = eta S and S>0,
-- cancellation therefore gives
--
--   eta <= 2 g.
--
-- Consequently any nonnegative self-leg eigenvalue-difference magnitude d
-- with d <= 2 H obeys
--
--   eta d M <= 4 g H M,     M>=0.
--
-- This file closes that normal-form algebra.  The literal physical weld from
-- the Round102 Waleffe-Heron high-minority numerator to the post-division
-- coefficient premise c<=2LH is intentionally left visible: the repository
-- currently has the division-free numerator gain, but no dedicated owner that
-- identifies that exact premise on the Round109 phase cell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; _<_; NonNegative; Positive; nonNegative; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNHeterochiralGapRelativeDampingRound106Exact as Gap
import DASHI.Physics.Closure.NSTriadKNWaleffeHHMinorityNumeratorGainRound102Exact as Numerator

record HighMinoritySelfNormalFormDatum : Set where
  constructor high-minority-self-normal-form-datum
  field
    geometry : Gap.GapDampingGeometry
    coefficient normalFormWeight : ℚ
    dampingScalePositive : 0ℚ < Gap.dampingScale geometry
    improvedCoefficientBound :
      coefficient ≤ Gap.two * (Gap.low geometry * Gap.high geometry)
    normalFormFactorization :
      coefficient ≡ normalFormWeight * Gap.dampingScale geometry

open HighMinoritySelfNormalFormDatum public

twoGap : HighMinoritySelfNormalFormDatum → ℚ
twoGap D = Gap.two * Gap.gap (geometry D)

highMinorityNormalFormWeightBelowTwoGap :
  (D : HighMinoritySelfNormalFormDatum) →
  normalFormWeight D ≤ twoGap D
highMinorityNormalFormWeightBelowTwoGap D =
  let
    S = Gap.dampingScale (geometry D)
    eta = normalFormWeight D
    upper = twoGap D

    coefficientBound : coefficient D ≤ upper * S
    coefficientBound =
      Gap.highMinorityImprovedCoefficientHasSingleGap
        (geometry D) (coefficient D) (improvedCoefficientBound D)

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

highMinoritySelfLegCarriesOneGapPower :
  (D : HighMinoritySelfNormalFormDatum) →
  (selfDifference squareMass : ℚ) →
  0ℚ ≤ selfDifference →
  selfDifference ≤ Gap.two * Gap.high (geometry D) →
  0ℚ ≤ squareMass →
  normalFormWeight D * selfDifference * squareMass
  ≤
  ((Gap.two * Gap.two) * Gap.gap (geometry D) * Gap.high (geometry D))
    * squareMass
highMinoritySelfLegCarriesOneGapPower D selfDifference squareMass
    selfDifferenceNN selfDifferenceBound squareMassNN =
  let
    etaBound = highMinorityNormalFormWeightBelowTwoGap D
    etaUpper = twoGap D
    high = Gap.high (geometry D)

    etaUpperNN : 0ℚ ≤ etaUpper
    etaUpperNN =
      let
        instance twoNNI = nonNegative Gap.twoNonnegative
        gapNNI = nonNegative (Gap.gapNonnegative (geometry D))
      in ℚP.nonNegative⁻¹ etaUpper

    first :
      normalFormWeight D * selfDifference
      ≤ etaUpper * selfDifference
    first =
      let instance diffNNI = nonNegative selfDifferenceNN
      in ℚP.*-monoʳ-≤-nonNeg selfDifference etaBound

    second :
      etaUpper * selfDifference
      ≤ etaUpper * (Gap.two * high)
    second =
      let instance upperNNI = nonNegative etaUpperNN
      in ℚP.*-monoˡ-≤-nonNeg etaUpper selfDifferenceBound

    endpoint :
      etaUpper * (Gap.two * high)
      ≡ (Gap.two * Gap.two) * Gap.gap (geometry D) * high
    endpoint = solve (Gap.gap (geometry D) ∷ high ∷ [])

    coefficientBound :
      normalFormWeight D * selfDifference
      ≤ (Gap.two * Gap.two) * Gap.gap (geometry D) * high
    coefficientBound =
      ℚP.≤-trans first
        (subst
          (λ upper → etaUpper * selfDifference ≤ upper)
          endpoint second)
  in
  let instance massNNI = nonNegative squareMassNN
  in ℚP.*-monoʳ-≤-nonNeg squareMass coefficientBound

round109HighMinorityNormalFormOneGapAlgebraClosed : Bool
round109HighMinorityNormalFormOneGapAlgebraClosed = true

round109Round102HighMinorityNumeratorGainReused : Bool
round109Round102HighMinorityNumeratorGainReused =
  Numerator.round102HighMinorityHHWaleffeNumeratorGainClosed

round109PhysicalHighMinorityPostDivisionCoefficientWeldClosed : Bool
round109PhysicalHighMinorityPostDivisionCoefficientWeldClosed = false

round109CompleteHighMinoritySelfPhasePaymentClosed : Bool
round109CompleteHighMinoritySelfPhasePaymentClosed = false

round109HighMinorityNormalFormOneGapAlgebraClosedIsTrue :
  round109HighMinorityNormalFormOneGapAlgebraClosed ≡ true
round109HighMinorityNormalFormOneGapAlgebraClosedIsTrue = refl

round109Round102HighMinorityNumeratorGainReusedIsTrue :
  round109Round102HighMinorityNumeratorGainReused ≡ true
round109Round102HighMinorityNumeratorGainReusedIsTrue = refl

round109PhysicalHighMinorityPostDivisionCoefficientWeldClosedIsFalse :
  round109PhysicalHighMinorityPostDivisionCoefficientWeldClosed ≡ false
round109PhysicalHighMinorityPostDivisionCoefficientWeldClosedIsFalse = refl

round109CompleteHighMinoritySelfPhasePaymentClosedIsFalse :
  round109CompleteHighMinoritySelfPhasePaymentClosed ≡ false
round109CompleteHighMinoritySelfPhasePaymentClosedIsFalse = refl
