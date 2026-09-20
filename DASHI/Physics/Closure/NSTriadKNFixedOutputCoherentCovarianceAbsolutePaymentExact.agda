module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceAbsolutePaymentExact where

------------------------------------------------------------------------
-- S2b2d1b2 / COMPLETE-GRAPH COVARIANCE ABSOLUTE PAYMENT
--
-- d1b2 gives the exact signed covariance numerator
--
--   PairCov = sum_{i<j} (r_i-r_j)(w_i-w_j).
--
-- The work-difference bridge proves
--
--   |w_i-w_j| <= 2 ( ||M||^2 + ||A_i-A_j||^2 ).
--
-- This owner lifts that LOCAL theorem over the whole complete graph without
-- inventing any separation, sign, or cutoff-independent constant:
--
--   |PairCov|
--     <= 2 sum_{i<j}
--          |r_i-r_j| ( ||M||^2 + ||A_i-A_j||^2 ).
--
-- This is the exact unconditional quantitative d1b2 reduction.  Any stronger
-- Clay-facing payment must now control this literal rate-weighted pair energy;
-- the scalar Hermitian/covariance algebra itself is closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Bridge

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

pairAbsoluteMajorant :
  ∀ {A : Set} →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  C3.Complex3 F →
  A → A → ℚ
pairAbsoluteMajorant rate value mixed left right =
  two *
    (∣ rate left - rate right ∣ *
      (L2.complex3NormSquared mixed
        + L2.complex3NormSquared
            (C3.complex3Subtract (value left) (value right))))

majorantAgainstHead :
  ∀ {A : Set} →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  C3.Complex3 F →
  A → List A → ℚ
majorantAgainstHead rate value mixed head [] = 0ℚ
majorantAgainstHead rate value mixed head (x ∷ xs) =
  pairAbsoluteMajorant rate value mixed head x
  + majorantAgainstHead rate value mixed head xs

pairAbsoluteMajorantSum :
  ∀ {A : Set} →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  C3.Complex3 F →
  List A → ℚ
pairAbsoluteMajorantSum rate value mixed [] = 0ℚ
pairAbsoluteMajorantSum rate value mixed (x ∷ xs) =
  majorantAgainstHead rate value mixed x xs
  + pairAbsoluteMajorantSum rate value mixed xs

absProductBound :
  (a b B : ℚ) →
  ∣ b ∣ ≤ B →
  ∣ a * b ∣ ≤ ∣ a ∣ * B
absProductBound a b B bBound =
  let
    absA0 : 0ℚ ≤ ∣ a ∣
    absA0 = ℚP.0≤∣p∣ a

    scaled :
      ∣ a ∣ * ∣ b ∣ ≤ ∣ a ∣ * B
    scaled = ℚP.*-monoˡ-≤-nonNeg ∣ a ∣ bBound
  in
  subst
    (_≤ ∣ a ∣ * B)
    (sym (ℚP.∣p*q∣≡∣p∣*∣q∣ a b))
    scaled

singlePairCovarianceBound :
  ∀ {A : Set}
    (rate : A → ℚ)
    (value : A → C3.Complex3 F)
    (mixed : C3.Complex3 F)
    (left right : A) →
  ∣ (rate left - rate right)
      * (Work.coherentWork mixed (value left)
          - Work.coherentWork mixed (value right)) ∣
  ≤ pairAbsoluteMajorant rate value mixed left right
singlePairCovarianceBound rate value mixed left right =
  let
    dr = rate left - rate right
    dw =
      Work.coherentWork mixed (value left)
      - Work.coherentWork mixed (value right)
    local =
      Bridge.coherentWorkDifferenceMagnitudeBound
        mixed (value left) (value right)
    first =
      absProductBound dr dw
        (two *
          (L2.complex3NormSquared mixed
            + L2.complex3NormSquared
                (C3.complex3Subtract (value left) (value right))))
        local
  in
  first

absAddBound :
  (x y X Y : ℚ) →
  ∣ x ∣ ≤ X →
  ∣ y ∣ ≤ Y →
  ∣ x + y ∣ ≤ X + Y
absAddBound x y X Y xBound yBound =
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣ x y)
    (ℚP.+-mono-≤ xBound yBound)

pairAgainstHeadAbsoluteBound :
  ∀ {A : Set}
    (rate : A → ℚ)
    (value : A → C3.Complex3 F)
    (mixed : C3.Complex3 F)
    (head : A)
    (items : List A) →
  ∣ Pair.pairAgainstHead
      rate
      (λ i → Work.coherentWork mixed (value i))
      head items ∣
  ≤ majorantAgainstHead rate value mixed head items
pairAgainstHeadAbsoluteBound rate value mixed head [] =
  ℚP.≤-refl
pairAgainstHeadAbsoluteBound rate value mixed head (x ∷ xs) =
  absAddBound
    ((rate head - rate x)
      * (Work.coherentWork mixed (value head)
          - Work.coherentWork mixed (value x)))
    (Pair.pairAgainstHead
      rate
      (λ i → Work.coherentWork mixed (value i))
      head xs)
    (pairAbsoluteMajorant rate value mixed head x)
    (majorantAgainstHead rate value mixed head xs)
    (singlePairCovarianceBound rate value mixed head x)
    (pairAgainstHeadAbsoluteBound rate value mixed head xs)

pairDifferenceWorkAbsoluteBound :
  ∀ {A : Set}
    (rate : A → ℚ)
    (value : A → C3.Complex3 F)
    (mixed : C3.Complex3 F)
    (items : List A) →
  ∣ Pair.pairDifferenceWorkSum
      rate
      (λ i → Work.coherentWork mixed (value i))
      items ∣
  ≤ pairAbsoluteMajorantSum rate value mixed items
pairDifferenceWorkAbsoluteBound rate value mixed [] =
  ℚP.≤-refl
pairDifferenceWorkAbsoluteBound rate value mixed (x ∷ xs) =
  absAddBound
    (Pair.pairAgainstHead
      rate
      (λ i → Work.coherentWork mixed (value i))
      x xs)
    (Pair.pairDifferenceWorkSum
      rate
      (λ i → Work.coherentWork mixed (value i))
      xs)
    (majorantAgainstHead rate value mixed x xs)
    (pairAbsoluteMajorantSum rate value mixed xs)
    (pairAgainstHeadAbsoluteBound rate value mixed x xs)
    (pairDifferenceWorkAbsoluteBound rate value mixed xs)

completeGraphCovarianceAbsolutePaymentClosed : Bool
completeGraphCovarianceAbsolutePaymentClosed = true

workDifferenceScalarOracleEliminated : Bool
workDifferenceScalarOracleEliminated = true

rateWeightedPairEnergyUniformlyPaidHere : Bool
rateWeightedPairEnergyUniformlyPaidHere = false

clayPromotion : Bool
clayPromotion = false

completeGraphCovarianceAbsolutePaymentClosedIsTrue :
  completeGraphCovarianceAbsolutePaymentClosed ≡ true
completeGraphCovarianceAbsolutePaymentClosedIsTrue = refl

workDifferenceScalarOracleEliminatedIsTrue :
  workDifferenceScalarOracleEliminated ≡ true
workDifferenceScalarOracleEliminatedIsTrue = refl

rateWeightedPairEnergyUniformlyPaidHereIsFalse :
  rateWeightedPairEnergyUniformlyPaidHere ≡ false
rateWeightedPairEnergyUniformlyPaidHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
