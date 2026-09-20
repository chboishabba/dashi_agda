module DASHI.Physics.Closure.NSTriadKNCenteredCovarianceToSecondMomentExact where

------------------------------------------------------------------------
-- PERIODIC B / CENTERED COVARIANCE -> PURE FIRST-ORDER SECOND MOMENT
--
-- The exact fixed-output covariance recut has already removed the common
-- output-frequency contribution and exposed each remaining pair as
--
--   weight * (Delta multiplier) * (Delta work).
--
-- This is strictly simpler than the generic R571 Taylor sample.  There is no
-- second-order Taylor remainder in this normal form.  If
--
--   |Delta multiplier| <= d A1
--   |Delta work|       <= d G2,
--
-- then, with weight >= 0,
--
--   weight (Delta multiplier)(Delta work)
--     <= weight |Delta multiplier| |Delta work|
--     <= weight d^2 A1 G2.
--
-- The canonical PairedSecondMomentSample below therefore has
--
--   linearIncrement      = |Delta multiplier|
--   derivativeDifference = |Delta work|
--   plusRemainder        = 0
--   minusRemainder       = 0
--
-- and its pairedMagnitude is EXACTLY the absolute first-order product.
--
-- This is the theorem-level bridge between the physical centered-covariance
-- normal form and the existing R571 M2 currency.  It introduces no fibre
-- cardinality factor, no Taylor-curvature charge, and no positivity assumption
-- on the signed covariance product itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment

record CenteredCovarianceSecondMomentPair : Set where
  constructor centered-covariance-second-moment-pair
  field
    weight displacement : ℚ
    multiplierDifference workDifference : ℚ
    transportGradient stateGradient : ℚ

    weightNonnegative : 0ℚ ≤ weight
    displacementNonnegative : 0ℚ ≤ displacement
    transportGradientNonnegative : 0ℚ ≤ transportGradient
    stateGradientNonnegative : 0ℚ ≤ stateGradient

    multiplierDifferenceBound :
      ∣ multiplierDifference ∣
      ≤ displacement * transportGradient

    workDifferenceBound :
      ∣ workDifference ∣
      ≤ displacement * stateGradient

open CenteredCovarianceSecondMomentPair public

signedCovariancePair : CenteredCovarianceSecondMomentPair → ℚ
signedCovariancePair P =
  weight P * (multiplierDifference P * workDifference P)

covarianceSecondMomentSample :
  CenteredCovarianceSecondMomentPair →
  Moment.PairedSecondMomentSample
covarianceSecondMomentSample P =
  Moment.paired-second-moment-sample
    (weight P)
    (displacement P)
    ∣ multiplierDifference P ∣
    ∣ workDifference P ∣
    0ℚ
    0ℚ
    0ℚ
    0ℚ
    (weightNonnegative P)
    (displacementNonnegative P)
    (ℚP.0≤∣p∣ (multiplierDifference P))
    (ℚP.0≤∣p∣ (workDifference P))
    ℚP.≤-refl
    ℚP.≤-refl
    ℚP.≤-refl
    ℚP.≤-refl

covarianceSampleMagnitudeMeaning :
  (P : CenteredCovarianceSecondMomentPair) →
  Moment.pairedMagnitude (covarianceSecondMomentSample P)
  ≡ weight P * (∣ multiplierDifference P ∣ * ∣ workDifference P ∣)
covarianceSampleMagnitudeMeaning P =
  solve
    ( weight P
    ∷ ∣ multiplierDifference P ∣
    ∷ ∣ workDifference P ∣
    ∷ [] )

signedCovariancePairBelowSampleMagnitude :
  (P : CenteredCovarianceSecondMomentPair) →
  signedCovariancePair P
  ≤ Moment.pairedMagnitude (covarianceSecondMomentSample P)
signedCovariancePairBelowSampleMagnitude P =
  let
    rawProduct = multiplierDifference P * workDifference P

    rawBelowAbs :
      rawProduct ≤ ∣ rawProduct ∣
    rawBelowAbs = ℚP.p≤∣p∣ rawProduct

    absoluteProduct :
      ∣ rawProduct ∣
      ≡ ∣ multiplierDifference P ∣ * ∣ workDifference P ∣
    absoluteProduct =
      ℚP.∣p*q∣≡∣p∣*∣q∣
        (multiplierDifference P) (workDifference P)

    scaled :
      weight P * rawProduct
      ≤ weight P * (∣ multiplierDifference P ∣ * ∣ workDifference P ∣)
    scaled =
      let instance weightNNI = nonNegative (weightNonnegative P)
      in
      ℚP.*-monoˡ-≤-nonNeg
        (weight P)
        (subst
          (rawProduct ≤_)
          absoluteProduct
          rawBelowAbs)
  in
  subst
    (signedCovariancePair P ≤_)
    (sym (covarianceSampleMagnitudeMeaning P))
    scaled

covarianceSampleFirstOrderBound :
  (P : CenteredCovarianceSecondMomentPair) →
  Moment.pairedMagnitude (covarianceSecondMomentSample P)
  ≤
  Moment.weightedSecondMoment (covarianceSecondMomentSample P)
    * (transportGradient P * stateGradient P)
covarianceSampleFirstOrderBound P =
  let
    d = displacement P
    A1 = transportGradient P
    G2 = stateGradient P
    dm = ∣ multiplierDifference P ∣
    dw = ∣ workDifference P ∣

    dA1NN : 0ℚ ≤ d * A1
    dA1NN =
      Moment.productNonnegative d A1
        (displacementNonnegative P)
        (transportGradientNonnegative P)

    dG2NN : 0ℚ ≤ d * G2
    dG2NN =
      Moment.productNonnegative d G2
        (displacementNonnegative P)
        (stateGradientNonnegative P)

    productBound :
      dm * dw ≤ (d * A1) * (d * G2)
    productBound =
      Moment.multiplyBounds
        (ℚP.0≤∣p∣ (multiplierDifference P))
        dA1NN
        (ℚP.0≤∣p∣ (workDifference P))
        dG2NN
        (multiplierDifferenceBound P)
        (workDifferenceBound P)

    weightedProductBound :
      weight P * (dm * dw)
      ≤ weight P * ((d * A1) * (d * G2))
    weightedProductBound =
      let instance weightNNI = nonNegative (weightNonnegative P)
      in ℚP.*-monoˡ-≤-nonNeg (weight P) productBound

    endpoint :
      weight P * ((d * A1) * (d * G2))
      ≡
      Moment.weightedSecondMoment (covarianceSecondMomentSample P)
        * (A1 * G2)
    endpoint =
      solve (weight P ∷ d ∷ A1 ∷ G2 ∷ [])
  in
  subst
    ( Moment.pairedMagnitude (covarianceSecondMomentSample P) ≤_)
    endpoint
    (subst
      (λ lower →
        lower ≤ weight P * ((d * A1) * (d * G2)))
      (sym (covarianceSampleMagnitudeMeaning P))
      weightedProductBound)

signedCovariancePairBelowWeightedSecondMoment :
  (P : CenteredCovarianceSecondMomentPair) →
  signedCovariancePair P
  ≤
  Moment.weightedSecondMoment (covarianceSecondMomentSample P)
    * (transportGradient P * stateGradient P)
signedCovariancePairBelowWeightedSecondMoment P =
  ℚP.≤-trans
    (signedCovariancePairBelowSampleMagnitude P)
    (covarianceSampleFirstOrderBound P)

------------------------------------------------------------------------
-- Finite family aggregation.
------------------------------------------------------------------------

sumSignedCovariance :
  List CenteredCovarianceSecondMomentPair → ℚ
sumSignedCovariance [] = 0ℚ
sumSignedCovariance (P ∷ rest) =
  signedCovariancePair P + sumSignedCovariance rest

sumWeightedCovarianceM2 :
  List CenteredCovarianceSecondMomentPair → ℚ
sumWeightedCovarianceM2 [] = 0ℚ
sumWeightedCovarianceM2 (P ∷ rest) =
  Moment.weightedSecondMoment (covarianceSecondMomentSample P)
  + sumWeightedCovarianceM2 rest

sumLocalCovarianceM2Budget :
  List CenteredCovarianceSecondMomentPair → ℚ
sumLocalCovarianceM2Budget [] = 0ℚ
sumLocalCovarianceM2Budget (P ∷ rest) =
  Moment.weightedSecondMoment (covarianceSecondMomentSample P)
    * (transportGradient P * stateGradient P)
  + sumLocalCovarianceM2Budget rest

finiteSignedCovarianceBelowLocalM2Budget :
  (pairs : List CenteredCovarianceSecondMomentPair) →
  sumSignedCovariance pairs ≤ sumLocalCovarianceM2Budget pairs
finiteSignedCovarianceBelowLocalM2Budget [] = ℚP.≤-refl
finiteSignedCovarianceBelowLocalM2Budget (P ∷ rest) =
  ℚP.+-mono-≤
    (signedCovariancePairBelowWeightedSecondMoment P)
    (finiteSignedCovarianceBelowLocalM2Budget rest)

record UniformCenteredCovarianceSecondMomentFamily : Set₁ where
  field
    pairs : List CenteredCovarianceSecondMomentPair
    commonTransportGradient commonStateGradient : ℚ
    commonTransportGradientNonnegative : 0ℚ ≤ commonTransportGradient
    commonStateGradientNonnegative : 0ℚ ≤ commonStateGradient

    transportGradientUniform :
      (P : CenteredCovarianceSecondMomentPair) →
      P ∈ pairs →
      transportGradient P ≤ commonTransportGradient

    stateGradientUniform :
      (P : CenteredCovarianceSecondMomentPair) →
      P ∈ pairs →
      stateGradient P ≤ commonStateGradient

open UniformCenteredCovarianceSecondMomentFamily public

-- Pointwise uniformization is separated from the signed-to-M2 bridge so the
-- physical realization may choose the sharp local A1/G2 or one common family
-- envelope.  No pair-count factor is introduced by either choice.

centeredCovarianceUsesOnlyFirstOrderM2 : Bool
centeredCovarianceUsesOnlyFirstOrderM2 = true

centeredCovarianceTaylorCurvatureChargeRequired : Bool
centeredCovarianceTaylorCurvatureChargeRequired = false

centeredCovarianceSignedObserverDelayedUntilPairProduct : Bool
centeredCovarianceSignedObserverDelayedUntilPairProduct = true

centeredCovariancePairToR571SampleClosed : Bool
centeredCovariancePairToR571SampleClosed = true

clayPromotion : Bool
clayPromotion = false
