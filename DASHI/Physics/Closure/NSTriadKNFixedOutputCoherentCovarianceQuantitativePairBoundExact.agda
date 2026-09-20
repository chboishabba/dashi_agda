module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceQuantitativePairBoundExact where

------------------------------------------------------------------------
-- S2b2d1b2 / SIGNED PAIR-DIFFERENCE -> QUANTITATIVE SAME-PAIR BUDGET
--
-- The exact d1b2 centering theorem produces
--
--   sum_{i<j} (r_i-r_j)(w_i-w_j).
--
-- This owner performs the first genuinely quantitative step without changing
-- the finite graph:
--
--   signed pair sum
--     <= sum_{i<j} |r_i-r_j| |w_i-w_j|.
--
-- For coherent work w_i = 2 Re<M,A_i>, the existing literal Hermitian bridge
-- then gives on EACH SAME PAIR
--
--   |w_i-w_j|
--     <= 2 ( ||M||^2 + ||A_i-A_j||^2 ).
--
-- Therefore
--
--   pairDifferenceWorkSum
--     <= sum_{i<j} |r_i-r_j|
--          * 2 (||M||^2 + ||A_i-A_j||^2).
--
-- No n-factor, maximum extraction, fibre cardinality, shell estimate, or
-- spacetime majorization enters.  The remaining analytic theorem is precisely
-- a payment of this literal rate-weighted quotient-difference family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Bridge

F : C3.RealField _
F = Rational.rationalRealField

absolutePairTerm :
  ∀ {A : Set} →
  (A → ℚ) → (A → ℚ) → A → A → ℚ
absolutePairTerm rate work left right =
  ∣ rate left - rate right ∣ * ∣ work left - work right ∣

absoluteAgainstHead :
  ∀ {A : Set} →
  (A → ℚ) → (A → ℚ) → A → List A → ℚ
absoluteAgainstHead rate work head [] = 0ℚ
absoluteAgainstHead rate work head (x ∷ xs) =
  absolutePairTerm rate work head x
  + absoluteAgainstHead rate work head xs

absolutePairDifferenceSum :
  ∀ {A : Set} →
  (A → ℚ) → (A → ℚ) → List A → ℚ
absolutePairDifferenceSum rate work [] = 0ℚ
absolutePairDifferenceSum rate work (x ∷ xs) =
  absoluteAgainstHead rate work x xs
  + absolutePairDifferenceSum rate work xs

signedPairTermBelowAbsolute :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (left right : A) →
  (rate left - rate right) * (work left - work right)
  ≤ absolutePairTerm rate work left right
signedPairTermBelowAbsolute rate work left right =
  let
    x = rate left - rate right
    y = work left - work right
    raw : x * y ≤ ∣ x * y ∣
    raw = ℚP.p≤∣p∣ (x * y)
    meaning : ∣ x * y ∣ ≡ ∣ x ∣ * ∣ y ∣
    meaning = ℚP.∣p*q∣≡∣p∣*∣q∣ x y
  in
  subst (λ upper → x * y ≤ upper) meaning raw

pairAgainstHeadBelowAbsolute :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (head : A) →
  (rest : List A) →
  Pair.pairAgainstHead rate work head rest
  ≤ absoluteAgainstHead rate work head rest
pairAgainstHeadBelowAbsolute rate work head [] = ℚP.≤-refl
pairAgainstHeadBelowAbsolute rate work head (x ∷ xs) =
  ℚP.+-mono-≤
    (signedPairTermBelowAbsolute rate work head x)
    (pairAgainstHeadBelowAbsolute rate work head xs)

pairDifferenceWorkSumBelowAbsolute :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (items : List A) →
  Pair.pairDifferenceWorkSum rate work items
  ≤ absolutePairDifferenceSum rate work items
pairDifferenceWorkSumBelowAbsolute rate work [] = ℚP.≤-refl
pairDifferenceWorkSumBelowAbsolute rate work (x ∷ xs) =
  ℚP.+-mono-≤
    (pairAgainstHeadBelowAbsolute rate work x xs)
    (pairDifferenceWorkSumBelowAbsolute rate work xs)


absolutePairAgainstHeadBound :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (head : A) →
  (rest : List A) →
  ∣ Pair.pairAgainstHead rate work head rest ∣
  ≤ absoluteAgainstHead rate work head rest
absolutePairAgainstHeadBound rate work head [] =
  subst
    (λ left → left ≤ 0ℚ)
    (ℚP.0≤p⇒∣p∣≡p ℚP.≤-refl)
    ℚP.≤-refl
absolutePairAgainstHeadBound rate work head (x ∷ xs) =
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      ((rate head - rate x) * (work head - work x))
      (Pair.pairAgainstHead rate work head xs))
    (ℚP.+-mono-≤
      (subst
        (λ upper →
          ∣ (rate head - rate x) * (work head - work x) ∣ ≤ upper)
        (ℚP.∣p*q∣≡∣p∣*∣q∣
          (rate head - rate x) (work head - work x))
        ℚP.≤-refl)
      (absolutePairAgainstHeadBound rate work head xs))

absolutePairDifferenceWorkSumBound :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (items : List A) →
  ∣ Pair.pairDifferenceWorkSum rate work items ∣
  ≤ absolutePairDifferenceSum rate work items
absolutePairDifferenceWorkSumBound rate work [] =
  subst
    (λ left → left ≤ 0ℚ)
    (ℚP.0≤p⇒∣p∣≡p ℚP.≤-refl)
    ℚP.≤-refl
absolutePairDifferenceWorkSumBound rate work (x ∷ xs) =
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      (Pair.pairAgainstHead rate work x xs)
      (Pair.pairDifferenceWorkSum rate work xs))
    (ℚP.+-mono-≤
      (absolutePairAgainstHeadBound rate work x xs)
      (absolutePairDifferenceWorkSumBound rate work xs))

negativePairDifferenceWorkSumBelowAbsolute :
  ∀ {A : Set} →
  (rate work : A → ℚ) →
  (items : List A) →
  0ℚ - Pair.pairDifferenceWorkSum rate work items
  ≤ absolutePairDifferenceSum rate work items
negativePairDifferenceWorkSumBelowAbsolute rate work items =
  let
    x = Pair.pairDifferenceWorkSum rate work items
    raw : 0ℚ - x ≤ ∣ 0ℚ - x ∣
    raw = ℚP.p≤∣p∣ (0ℚ - x)

    negMeaning : 0ℚ - x ≡ - x
    negMeaning = solve (x ∷ [])

    absMeaning : ∣ 0ℚ - x ∣ ≡ ∣ x ∣
    absMeaning =
      trans
        (cong ∣_∣ negMeaning)
        (ℚP.∣-p∣≡∣p∣ x)

    first : 0ℚ - x ≤ ∣ x ∣
    first =
      subst
        (λ upper → 0ℚ - x ≤ upper)
        absMeaning
        raw
  in
  ℚP.≤-trans first
    (absolutePairDifferenceWorkSumBound rate work items)

------------------------------------------------------------------------
-- Coherent-work specialization: retain the exact pair topology.
------------------------------------------------------------------------

rateWeightedYoungPair :
  ∀ {A : Set} →
  C3.Complex3 F →
  (A → ℚ) →
  (A → C3.Complex3 F) →
  A → A → ℚ
rateWeightedYoungPair mixed rate value left right =
  ∣ rate left - rate right ∣
  * Bridge.two
      * ( L2.complex3NormSquared mixed
        + L2.complex3NormSquared
            (C3.complex3Subtract (value left) (value right)) )

rateWeightedYoungAgainstHead :
  ∀ {A : Set} →
  C3.Complex3 F →
  (A → ℚ) →
  (A → C3.Complex3 F) →
  A → List A → ℚ
rateWeightedYoungAgainstHead mixed rate value head [] = 0ℚ
rateWeightedYoungAgainstHead mixed rate value head (x ∷ xs) =
  rateWeightedYoungPair mixed rate value head x
  + rateWeightedYoungAgainstHead mixed rate value head xs

rateWeightedYoungPairSum :
  ∀ {A : Set} →
  C3.Complex3 F →
  (A → ℚ) →
  (A → C3.Complex3 F) →
  List A → ℚ
rateWeightedYoungPairSum mixed rate value [] = 0ℚ
rateWeightedYoungPairSum mixed rate value (x ∷ xs) =
  rateWeightedYoungAgainstHead mixed rate value x xs
  + rateWeightedYoungPairSum mixed rate value xs

absoluteCoherentPairBelowYoung :
  ∀ {A : Set} →
  (mixed : C3.Complex3 F) →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (left right : A) →
  absolutePairTerm
    rate
    (λ item → Work.coherentWork mixed (value item))
    left right
  ≤ rateWeightedYoungPair mixed rate value left right
absoluteCoherentPairBelowYoung mixed rate value left right =
  let
    rateDiff = rate left - rate right
    workDiff =
      Work.coherentWork mixed (value left) - Work.coherentWork mixed (value right)
    difference = C3.complex3Subtract (value left) (value right)
    envelope =
      Bridge.two *
        (L2.complex3NormSquared mixed
          + L2.complex3NormSquared difference)

    workBound : ∣ workDiff ∣ ≤ envelope
    workBound =
      Bridge.coherentWorkDifferenceMagnitudeBound
        mixed (value left) (value right)

    absRateNN : 0ℚ ≤ ∣ rateDiff ∣
    absRateNN = ℚP.0≤∣p∣ rateDiff

    absWorkNN : 0ℚ ≤ ∣ workDiff ∣
    absWorkNN = ℚP.0≤∣p∣ workDiff

    mixedNN : 0ℚ ≤ L2.complex3NormSquared mixed
    mixedNN = Separation.complex3NormSquaredNonnegative mixed

    differenceNN : 0ℚ ≤ L2.complex3NormSquared difference
    differenceNN = Separation.complex3NormSquaredNonnegative difference

    innerNN :
      0ℚ ≤ L2.complex3NormSquared mixed
        + L2.complex3NormSquared difference
    innerNN = Rational.addNonnegative mixedNN differenceNN

    oneNN : 0ℚ ≤ 1ℚ
    oneNN = ℚP.0≤∣p∣ 1ℚ

    twoNN : 0ℚ ≤ Bridge.two
    twoNN = Rational.addNonnegative oneNN oneNN

    envelopeNN : 0ℚ ≤ envelope
    envelopeNN =
      Rational.nonnegativeProductMonotone
        twoNN innerNN twoNN innerNN
        ℚP.≤-refl ℚP.≤-refl
    productBound :
      ∣ rateDiff ∣ * ∣ workDiff ∣
      ≤ ∣ rateDiff ∣ * envelope
    productBound =
      Rational.nonnegativeProductMonotone
        absRateNN absWorkNN absRateNN envelopeNN
        ℚP.≤-refl workBound

    targetMeaning :
      ∣ rateDiff ∣ * envelope
      ≡ rateWeightedYoungPair mixed rate value left right
    targetMeaning = solve
      ( ∣ rateDiff ∣
      ∷ Bridge.two
      ∷ L2.complex3NormSquared mixed
      ∷ L2.complex3NormSquared difference
      ∷ [])
  in
  subst
    (λ upper → ∣ rateDiff ∣ * ∣ workDiff ∣ ≤ upper)
    targetMeaning
    productBound

absoluteCoherentAgainstHeadBelowYoung :
  ∀ {A : Set} →
  (mixed : C3.Complex3 F) →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (head : A) →
  (rest : List A) →
  absoluteAgainstHead rate (λ item → Work.coherentWork mixed (value item)) head rest
  ≤ rateWeightedYoungAgainstHead mixed rate value head rest
absoluteCoherentAgainstHeadBelowYoung mixed rate value head [] = ℚP.≤-refl
absoluteCoherentAgainstHeadBelowYoung mixed rate value head (x ∷ xs) =
  ℚP.+-mono-≤
    (absoluteCoherentPairBelowYoung mixed rate value head x)
    (absoluteCoherentAgainstHeadBelowYoung mixed rate value head xs)

absoluteCoherentPairDifferenceBelowYoung :
  ∀ {A : Set} →
  (mixed : C3.Complex3 F) →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (items : List A) →
  absolutePairDifferenceSum
    rate (λ item → Work.coherentWork mixed (value item)) items
  ≤ rateWeightedYoungPairSum mixed rate value items
absoluteCoherentPairDifferenceBelowYoung mixed rate value [] = ℚP.≤-refl
absoluteCoherentPairDifferenceBelowYoung mixed rate value (x ∷ xs) =
  ℚP.+-mono-≤
    (absoluteCoherentAgainstHeadBelowYoung mixed rate value x xs)
    (absoluteCoherentPairDifferenceBelowYoung mixed rate value xs)

signedCoherentPairDifferenceBelowYoung :
  ∀ {A : Set} →
  (mixed : C3.Complex3 F) →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (items : List A) →
  Pair.pairDifferenceWorkSum
    rate (λ item → Work.coherentWork mixed (value item)) items
  ≤ rateWeightedYoungPairSum mixed rate value items
signedCoherentPairDifferenceBelowYoung mixed rate value items =
  ℚP.≤-trans
    (pairDifferenceWorkSumBelowAbsolute
      rate (λ item → Work.coherentWork mixed (value item)) items)
    (absoluteCoherentPairDifferenceBelowYoung mixed rate value items)


negativeCoherentPairDifferenceBelowYoung :
  ∀ {A : Set} →
  (mixed : C3.Complex3 F) →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (items : List A) →
  0ℚ - Pair.pairDifferenceWorkSum
    rate (λ item → Work.coherentWork mixed (value item)) items
  ≤ rateWeightedYoungPairSum mixed rate value items
negativeCoherentPairDifferenceBelowYoung mixed rate value items =
  ℚP.≤-trans
    (negativePairDifferenceWorkSumBelowAbsolute
      rate (λ item → Work.coherentWork mixed (value item)) items)
    (absoluteCoherentPairDifferenceBelowYoung mixed rate value items)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

signedPairDifferenceAbsoluteSameGraphBoundClosed : Bool
signedPairDifferenceAbsoluteSameGraphBoundClosed = true

absolutePairDifferenceSameGraphBoundClosed : Bool
absolutePairDifferenceSameGraphBoundClosed = true

negativePairDifferenceSameGraphBoundClosed : Bool
negativePairDifferenceSameGraphBoundClosed = true

coherentWorkPairDifferenceYoungBoundClosed : Bool
coherentWorkPairDifferenceYoungBoundClosed = true

pairDifferenceQuantitativeReductionIntroducesCardinalityTax : Bool
pairDifferenceQuantitativeReductionIntroducesCardinalityTax = false

physicalRateWeightedQuotientDifferencePaymentClosedHere : Bool
physicalRateWeightedQuotientDifferencePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

signedPairDifferenceAbsoluteSameGraphBoundClosedIsTrue :
  signedPairDifferenceAbsoluteSameGraphBoundClosed ≡ true
signedPairDifferenceAbsoluteSameGraphBoundClosedIsTrue = refl

coherentWorkPairDifferenceYoungBoundClosedIsTrue :
  coherentWorkPairDifferenceYoungBoundClosed ≡ true
coherentWorkPairDifferenceYoungBoundClosedIsTrue = refl

pairDifferenceQuantitativeReductionIntroducesCardinalityTaxIsFalse :
  pairDifferenceQuantitativeReductionIntroducesCardinalityTax ≡ false
pairDifferenceQuantitativeReductionIntroducesCardinalityTaxIsFalse = refl
