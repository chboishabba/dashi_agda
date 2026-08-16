module DASHI.Physics.Closure.NSTriadKNPreferredLambdaScalarFeasibilityRound63Exact where

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
-- ROUND 63 G CONTRIBUTION
--
-- Round62's preferred scalar gate already depends on HH-bad data only through
-- the product H=C_* K_bad.  Round63 therefore makes
--
--   Lambda_bad := C_* K_bad
--
-- the primitive scalar.  The preferred kernel-zero gate is exactly
--
--   2 Lambda_bad
--     + K S^2 / margin
--     + 1/16 < 1,
--
-- where margin=(r-q)-a>0.  No factorization of Lambda_bad is needed by the
-- final absorption theorem.
--
-- Exact rational elimination again gives the immediate kill-tests
--
--   Lambda_bad < 15/32,
--   K S^2 < (15/16 - 2 Lambda_bad) margin.
--
-- This aligns G with the direct-product HH-bad producer in Round63.
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

record PreferredLambdaScalarGate : Set where
  field
    badProduct criticalScale rootSum margin : ℚ

    badProductNonnegative : 0ℚ ≤ badProduct
    criticalScaleNonnegative : 0ℚ ≤ criticalScale
    rootSumNonnegative : 0ℚ ≤ rootSum
    marginPositive : 0ℚ < margin

  reciprocalMargin : ℚ
  reciprocalMargin =
    let instance marginNonzero = ℚ.>-nonZero marginPositive
    in ℚ.1/_ margin

  field
    strictGate :
      2 * badProduct
      + criticalScale * rootSum * rootSum * reciprocalMargin
      + oneSixteenth
      < 1ℚ

open PreferredLambdaScalarGate public

softNumerator : PreferredLambdaScalarGate → ℚ
softNumerator data = criticalScale data * rootSum data * rootSum data

reserve : PreferredLambdaScalarGate → ℚ
reserve data = fifteenSixteenths - 2 * badProduct data

softNumeratorNonnegative :
  (data : PreferredLambdaScalarGate) → 0ℚ ≤ softNumerator data
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
  (data : PreferredLambdaScalarGate) → 0ℚ < reciprocalMargin data
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
  (data : PreferredLambdaScalarGate) →
  0ℚ ≤ softNumerator data * reciprocalMargin data
softTermNonnegative data =
  let
    nNN = softNumeratorNonnegative data
    invNN = ℚP.<⇒≤ (reciprocalMarginPositive data)
    instance
      nNNI = nonNegative nNN
      invNNI = nonNegative invNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
        (softNumerator data) (reciprocalMargin data)
  in
  ℚP.nonNegative⁻¹
    (softNumerator data * reciprocalMargin data)

hardPlusBoundaryStrict :
  (data : PreferredLambdaScalarGate) →
  2 * badProduct data + oneSixteenth < 1ℚ
hardPlusBoundaryStrict data =
  let
    softNN = softTermNonnegative data
    lower :
      2 * badProduct data + oneSixteenth
      ≤ 2 * badProduct data
        + softNumerator data * reciprocalMargin data
        + oneSixteenth
    lower =
      ℚP.+-monoʳ-≤ oneSixteenth
        (ℚP.+-monoˡ-≤ (2 * badProduct data) softNN)
  in
  ℚP.≤-<-trans lower (strictGate data)

badProductBelow15Over32 :
  (data : PreferredLambdaScalarGate) →
  badProduct data < fifteenThirtySeconds
badProductBelow15Over32 data =
  let
    shifted : 2 * badProduct data < fifteenSixteenths
    shifted =
      let
        move = ℚP.+-monoʳ-< (0ℚ - oneSixteenth)
          (hardPlusBoundaryStrict data)
        leftMeaning :
          (2 * badProduct data + oneSixteenth)
            + (0ℚ - oneSixteenth)
          ≡ 2 * badProduct data
        leftMeaning = solve (badProduct data ∷ [])
        rightMeaning :
          1ℚ + (0ℚ - oneSixteenth) ≡ fifteenSixteenths
        rightMeaning = solve []
      in subst₂ _<_ leftMeaning rightMeaning move

    scaled :
      half * (2 * badProduct data)
      < half * fifteenSixteenths
    scaled =
      let instance halfPos = positive halfPositive
      in ℚP.*-monoˡ-<-pos half shifted

    leftMeaning : half * (2 * badProduct data) ≡ badProduct data
    leftMeaning = solve (badProduct data ∷ [])
    rightMeaning : half * fifteenSixteenths ≡ fifteenThirtySeconds
    rightMeaning = solve []
  in
  subst₂ _<_ leftMeaning rightMeaning scaled

softTermBelowReserve :
  (data : PreferredLambdaScalarGate) →
  softNumerator data * reciprocalMargin data < reserve data
softTermBelowReserve data =
  let
    hard = 2 * badProduct data
    soft = softNumerator data * reciprocalMargin data
    shifted = ℚP.+-monoʳ-< (0ℚ - (hard + oneSixteenth)) (strictGate data)
    leftMeaning :
      (hard + soft + oneSixteenth) + (0ℚ - (hard + oneSixteenth)) ≡ soft
    leftMeaning = solve (hard ∷ soft ∷ [])
    rightMeaning :
      1ℚ + (0ℚ - (hard + oneSixteenth)) ≡ reserve data
    rightMeaning = solve (hard ∷ badProduct data ∷ [])
  in
  subst₂ _<_ leftMeaning rightMeaning shifted

marginTimesReciprocalIsOne :
  (data : PreferredLambdaScalarGate) →
  margin data * reciprocalMargin data ≡ 1ℚ
marginTimesReciprocalIsOne data =
  let
    m = margin data
    instance mNonzero = ℚ.>-nonZero (marginPositive data)
  in
  ℚP.*-inverseʳ m

softNumeratorBelowReserveTimesMargin :
  (data : PreferredLambdaScalarGate) →
  softNumerator data < reserve data * margin data
softNumeratorBelowReserveTimesMargin data =
  let
    scaled :
      (softNumerator data * reciprocalMargin data) * margin data
      < reserve data * margin data
    scaled =
      let instance marginPos = positive (marginPositive data)
      in ℚP.*-monoˡ-<-pos (margin data) (softTermBelowReserve data)

    leftMeaning :
      (softNumerator data * reciprocalMargin data) * margin data
      ≡ softNumerator data
    leftMeaning =
      trans
        (solve (softNumerator data ∷ reciprocalMargin data ∷ margin data ∷ []))
        (trans
          (cong (softNumerator data *_)
            (marginTimesReciprocalIsOne data))
          (ℚP.*-identityʳ (softNumerator data)))
  in
  subst₂ _<_ leftMeaning refl scaled

preferredGateUsesLambdaBadDirectly : Bool
preferredGateUsesLambdaBadDirectly = true

preferredLambdaFeasibilityRegionSolvedExactly : Bool
preferredLambdaFeasibilityRegionSolvedExactly = true

preferredGateUsesLambdaBadDirectlyIsTrue :
  preferredGateUsesLambdaBadDirectly ≡ true
preferredGateUsesLambdaBadDirectlyIsTrue = refl

preferredLambdaFeasibilityRegionSolvedExactlyIsTrue :
  preferredLambdaFeasibilityRegionSolvedExactly ≡ true
preferredLambdaFeasibilityRegionSolvedExactlyIsTrue = refl
