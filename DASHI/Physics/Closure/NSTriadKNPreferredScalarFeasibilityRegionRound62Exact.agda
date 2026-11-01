module DASHI.Physics.Closure.NSTriadKNPreferredScalarFeasibilityRegionRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 62 CONTRIBUTION
--
-- Solve the preferred kernel-zero sharp gate into an explicit admissible
-- region.  Write
--
--   H = C_* K_bad,
--   N = K S^2,
--   m = (r-q)-a > 0.
--
-- The final gate is
--
--   2H + N/m + 1/16 < 1.
--
-- Exact rational algebra implies the two immediate falsifiers
--
--   H < 15/32,
--
--   N < (15/16 - 2H) m.
--
-- The second inequality is the correction-budget region after eliminating the
-- reciprocal.  Thus any physical constants outside this region kill the
-- current architecture before continuation/publishing concerns arise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; _≤_; _<_; 1/_; nonNegative; positive)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst₂; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

oneSixteenth fifteenSixteenths fifteenThirtySeconds half : ℚ
oneSixteenth = Int.+ 1 / 16
fifteenSixteenths = Int.+ 15 / 16
fifteenThirtySeconds = Int.+ 15 / 32
half = Int.+ 1 / 2

oneSixteenthNonnegative : 0ℚ ≤ oneSixteenth
oneSixteenthNonnegative = toWitness {a? = 0ℚ ≤? oneSixteenth} _

halfPositive : 0ℚ < half
halfPositive = toWitness {a? = 0ℚ <? half} _

record PreferredScalarGate : Set where
  field
    hhBadCeiling badChargeMultiplicity criticalScale rootSum margin : ℚ

    hhBadCeilingNonnegative : 0ℚ ≤ hhBadCeiling
    badChargeMultiplicityNonnegative : 0ℚ ≤ badChargeMultiplicity
    criticalScaleNonnegative : 0ℚ ≤ criticalScale
    rootSumNonnegative : 0ℚ ≤ rootSum
    marginPositive : 0ℚ < margin

  reciprocalMargin : ℚ
  reciprocalMargin =
    let instance marginNonzero = ℚ.>-nonZero marginPositive
    in ℚ.1/_ margin

  field
    strictGate :
      2 * hhBadCeiling * badChargeMultiplicity
      + criticalScale * rootSum * rootSum * reciprocalMargin
      + oneSixteenth
      < 1ℚ

open PreferredScalarGate public

hhBadProduct : PreferredScalarGate → ℚ
hhBadProduct data = hhBadCeiling data * badChargeMultiplicity data

softNumerator : PreferredScalarGate → ℚ
softNumerator data = criticalScale data * rootSum data * rootSum data

reserve : PreferredScalarGate → ℚ
reserve data = fifteenSixteenths - 2 * hhBadProduct data

softNumeratorNonnegative :
  (data : PreferredScalarGate) → 0ℚ ≤ softNumerator data
softNumeratorNonnegative data =
  let
    kNN = criticalScaleNonnegative data
    sNN = rootSumNonnegative data
    instance
      kNNI = nonNegative kNN
      sNNI = nonNegative sNN
      ksNNI = ℚP.nonNeg*nonNeg⇒nonNeg (criticalScale data) (rootSum data)
      kssNNI = ℚP.nonNeg*nonNeg⇒nonNeg
        (criticalScale data * rootSum data) (rootSum data)
  in
  ℚP.nonNegative⁻¹ (softNumerator data)

reciprocalMarginPositive :
  (data : PreferredScalarGate) → 0ℚ < reciprocalMargin data
reciprocalMarginPositive data =
  let
    m = margin data
    instance
      mPos = positive (marginPositive data)
      mNonzero = ℚP.pos⇒nonZero m
      invPos = ℚP.1/pos⇒pos m
  in
  ℚP.positive⁻¹ (reciprocalMargin data)

softTermNonnegative :
  (data : PreferredScalarGate) →
  0ℚ ≤ softNumerator data * reciprocalMargin data
softTermNonnegative data =
  let
    nNN = softNumeratorNonnegative data
    invNN = ℚP.<⇒≤ (reciprocalMarginPositive data)
    instance
      nNNI = nonNegative nNN
      invNNI = nonNegative invNN
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (softNumerator data) (reciprocalMargin data)
  in
  ℚP.nonNegative⁻¹
    (softNumerator data * reciprocalMargin data)

strictGateReassociated :
  (data : PreferredScalarGate) →
  2 * hhBadProduct data
    + softNumerator data * reciprocalMargin data
    + oneSixteenth
  < 1ℚ
strictGateReassociated data =
  subst₂ _<_
    (solve
      ( hhBadCeiling data ∷ badChargeMultiplicity data
      ∷ criticalScale data ∷ rootSum data
      ∷ reciprocalMargin data ∷ []))
    refl
    (strictGate data)

hhBadPlusBoundaryStrict :
  (data : PreferredScalarGate) →
  2 * hhBadProduct data + oneSixteenth < 1ℚ
hhBadPlusBoundaryStrict data =
  let
    softNN = softTermNonnegative data
    lower :
      2 * hhBadProduct data + oneSixteenth
      ≤ 2 * hhBadProduct data
        + softNumerator data * reciprocalMargin data
        + oneSixteenth
    lower =
      ℚP.+-monoʳ-≤ oneSixteenth
        (ℚP.+-monoˡ-≤ (2 * hhBadProduct data) softNN)
  in
  ℚP.≤-<-trans lower (strictGateReassociated data)

hhBadProductBelow15Over32 :
  (data : PreferredScalarGate) →
  hhBadProduct data < fifteenThirtySeconds
hhBadProductBelow15Over32 data =
  let
    shifted : 2 * hhBadProduct data < fifteenSixteenths
    shifted =
      let
        move = ℚP.+-monoʳ-< (0ℚ - oneSixteenth)
          (hhBadPlusBoundaryStrict data)
        leftMeaning :
          (2 * hhBadProduct data + oneSixteenth)
            + (0ℚ - oneSixteenth)
          ≡ 2 * hhBadProduct data
        leftMeaning = solve (hhBadProduct data ∷ [])
        rightMeaning :
          1ℚ + (0ℚ - oneSixteenth) ≡ fifteenSixteenths
        rightMeaning = solve []
      in subst₂ _<_ leftMeaning rightMeaning move

    scaled :
      half * (2 * hhBadProduct data)
      < half * fifteenSixteenths
    scaled =
      let instance halfPos = positive halfPositive
      in ℚP.*-monoˡ-<-pos half shifted

    leftMeaning : half * (2 * hhBadProduct data) ≡ hhBadProduct data
    leftMeaning = solve (hhBadProduct data ∷ [])
    rightMeaning : half * fifteenSixteenths ≡ fifteenThirtySeconds
    rightMeaning = solve []
  in
  subst₂ _<_ leftMeaning rightMeaning scaled

softTermBelowReserve :
  (data : PreferredScalarGate) →
  softNumerator data * reciprocalMargin data < reserve data
softTermBelowReserve data =
  let
    hard = 2 * hhBadProduct data
    soft = softNumerator data * reciprocalMargin data
    shifted = ℚP.+-monoʳ-< (0ℚ - (hard + oneSixteenth))
      (strictGateReassociated data)
    leftMeaning :
      (hard + soft + oneSixteenth)
        + (0ℚ - (hard + oneSixteenth))
      ≡ soft
    leftMeaning = solve (hard ∷ soft ∷ [])
    rightMeaning :
      1ℚ + (0ℚ - (hard + oneSixteenth))
      ≡ reserve data
    rightMeaning = solve (hard ∷ hhBadProduct data ∷ [])
  in
  subst₂ _<_ leftMeaning rightMeaning shifted

marginTimesReciprocalIsOne :
  (data : PreferredScalarGate) →
  margin data * reciprocalMargin data ≡ 1ℚ
marginTimesReciprocalIsOne data =
  let
    m = margin data
    instance mNonzero = ℚ.>-nonZero (marginPositive data)
  in
  ℚP.*-inverseʳ m

softNumeratorBelowReserveTimesMargin :
  (data : PreferredScalarGate) →
  softNumerator data < reserve data * margin data
softNumeratorBelowReserveTimesMargin data =
  let
    scaled :
      (softNumerator data * reciprocalMargin data) * margin data
      < reserve data * margin data
    scaled =
      let instance marginPos = positive (marginPositive data)
      in ℚP.*-monoˡ-<-pos
        (margin data) (softTermBelowReserve data)

    leftMeaning :
      (softNumerator data * reciprocalMargin data) * margin data
      ≡ softNumerator data
    leftMeaning =
      trans
        (solve
          (softNumerator data ∷ reciprocalMargin data ∷ margin data ∷ []))
        (trans
          (cong (softNumerator data *_)
            (marginTimesReciprocalIsOne data))
          (ℚP.*-identityʳ (softNumerator data)))
  in
  subst₂ _<_ leftMeaning refl scaled

preferredGateFeasibilityRegionSolvedExactly : Bool
preferredGateFeasibilityRegionSolvedExactly = true

preferredGateFeasibilityRegionSolvedExactlyIsTrue :
  preferredGateFeasibilityRegionSolvedExactly ≡ true
preferredGateFeasibilityRegionSolvedExactlyIsTrue = refl
