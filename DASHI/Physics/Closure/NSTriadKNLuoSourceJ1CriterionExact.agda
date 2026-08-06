module DASHI.Physics.Closure.NSTriadKNLuoSourceJ1CriterionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Compose the derived source estimates for J11 and J12 with weighted
-- time-window Cauchy.  The physical identification fields below only state
-- that the two Cauchy factors are the concrete J11 and J12 quantities;
-- neither factor bound nor the product estimate is supplied.
--
-- From
--
--   J11^2 <= 10 delta Q^2,
--   Q^3 J12^2 <= 640 delta,
--   Q >= 1,
--
-- the module derives the stronger square-safe estimate
--
--   J1^2 <= 6400 delta^2.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; subst₂; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePrefixJensenExact as Prefix
import DASHI.Physics.Closure.NSTriadKNLuoSourceWeightedJ11Exact as Source
import DASHI.Physics.Closure.NSTriadKNLuoSourceJ12FiveShellExact as Time
import DASHI.Physics.Closure.NSTriadKNLuoSourceJ1J2CombinationExact as Product
import DASHI.Physics.Closure.NSTriadKNLuoSourceJ11HalfRangeDerivedExact as J11
import DASHI.Physics.Closure.NSTriadKNLuoSourceJ12CriterionExact as J12

oneBelowFour : 1ℚ ≤ (Int.+ 4 / 1)
oneBelowFour = toWitness {a? = 1ℚ ≤? (Int.+ 4 / 1)} _

nonnegativeProduct :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
nonnegativeProduct {left} {right} leftNonnegative rightNonnegative =
  let
    instance
      leftIsNonnegative = nonNegative leftNonnegative
      rightIsNonnegative = nonNegative rightNonnegative
      productIsNonnegative = ℚₚ.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚₚ.nonNegative⁻¹ (left * right)

record SourceJ1CriterionData (TimeIndex : Set) : Set₁ where
  field
    j11Data : J11.SourceJ11HalfRangeData TimeIndex
    j12Data : J12.SourceJ12CriterionData TimeIndex
    j1Window : Product.FiniteSourceJ1Window TimeIndex

    j11FactorMeaning :
      Product.J11Squared j1Window
      ≡ J11.sourceJ11Squared j11Data

    j12FactorMeaning :
      Product.J12Squared j1Window
      ≡ J12.sourceJ12Square j12Data

    commonOutputScale :
      J12.outputScale j12Data
      ≡ Source.lambda (J11.outputShell j11Data)

    commonDelta :
      J12.delta j12Data ≡ J11.delta j11Data

open SourceJ1CriterionData public

outputScale : ∀ {TimeIndex} → SourceJ1CriterionData TimeIndex → ℚ
outputScale criterionData =
  Source.lambda (J11.outputShell (j11Data criterionData))

sourceJ1 : ∀ {TimeIndex} → SourceJ1CriterionData TimeIndex → ℚ
sourceJ1 criterionData = Product.J1 (j1Window criterionData)

outputScaleNonnegative :
  ∀ {TimeIndex} (criterionData : SourceJ1CriterionData TimeIndex) →
  0ℚ ≤ outputScale criterionData
outputScaleNonnegative criterionData =
  Prefix.powTwoNonnegative
    (J11.outputShell (j11Data criterionData))

outputScaleAtLeastOne :
  ∀ {TimeIndex} (criterionData : SourceJ1CriterionData TimeIndex) →
  1ℚ ≤ outputScale criterionData
outputScaleAtLeastOne criterionData =
  let
    j12 = j12Data criterionData
    lower = J12.lowerScale j12

    raw : 1ℚ * lower ≤ (Int.+ 4 / 1) * lower
    raw =
      let
        instance
          lowerIsNonnegative =
            nonNegative (J12.lowerScaleNonnegative j12)
      in
      ℚₚ.*-monoʳ-≤-nonNeg lower oneBelowFour

    leftMeaning : 1ℚ * lower ≡ lower
    leftMeaning = solve (lower ∷ [])

    lowerBelowFourLower : lower ≤ (Int.+ 4 / 1) * lower
    lowerBelowFourLower =
      subst
        (λ left → left ≤ (Int.+ 4 / 1) * lower)
        leftMeaning
        raw

    oneBelowJ12Output : 1ℚ ≤ J12.outputScale j12
    oneBelowJ12Output =
      subst
        (λ right → 1ℚ ≤ right)
        (sym (J12.outputScaleMeaning j12))
        (ℚₚ.≤-trans
          (J12.oneBelowLowerScale j12)
          lowerBelowFourLower)
  in
  subst
    (λ right → 1ℚ ≤ right)
    (commonOutputScale criterionData)
    oneBelowJ12Output

sourceJ11SquareNonnegative :
  ∀ {TimeIndex} (criterionData : SourceJ1CriterionData TimeIndex) →
  0ℚ ≤ J11.sourceJ11Squared (j11Data criterionData)
sourceJ11SquareNonnegative {TimeIndex} criterionData =
  go (J11.times (j11Data criterionData))
  where
  j11 = j11Data criterionData

  go :
    (remaining : List TimeIndex) →
    0ℚ ≤ Time.weightedTimeSum
      remaining
      (J11.timeWeight j11)
      (λ time →
        L2.square
          (Sum.sumTo
            (Source.sourceAmplitude
              (J11.normalizedAmplitude j11 time))
            (J11.outputShell j11)))
  go [] = ℚₚ.≤-refl
  go (time ∷ remaining) =
    L2.addNonnegative
      (nonnegativeProduct
        (J11.timeWeightNonnegative j11 time)
        (L2.squareNonnegative
          (Sum.sumTo
            (Source.sourceAmplitude
              (J11.normalizedAmplitude j11 time))
            (J11.outputShell j11))))
      (go remaining)

sourceJ1Cauchy :
  ∀ {TimeIndex} (criterionData : SourceJ1CriterionData TimeIndex) →
  L2.square (sourceJ1 criterionData)
  ≤ J11.sourceJ11Squared (j11Data criterionData)
      * J12.sourceJ12Square (j12Data criterionData)
sourceJ1Cauchy criterionData =
  subst
    (λ upper → L2.square (sourceJ1 criterionData) ≤ upper)
    (cong₂ _*_
      (j11FactorMeaning criterionData)
      (j12FactorMeaning criterionData))
    (Product.J1SquareBelowJ11J12 (j1Window criterionData))

outputSquaredBelowCubed :
  ∀ {TimeIndex} (criterionData : SourceJ1CriterionData TimeIndex) →
  L2.square (outputScale criterionData)
  ≤ J12.pow3 (outputScale criterionData)
outputSquaredBelowCubed criterionData =
  let
    q = outputScale criterionData
    qSquare = L2.square q

    scaled : qSquare * 1ℚ ≤ qSquare * q
    scaled =
      let
        instance
          squareIsNonnegative =
            nonNegative (L2.squareNonnegative q)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        qSquare (outputScaleAtLeastOne criterionData)

    leftMeaning : qSquare * 1ℚ ≡ qSquare
    leftMeaning = solve (qSquare ∷ [])

    rightMeaning : qSquare * q ≡ J12.pow3 q
    rightMeaning = solve (q ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning scaled

sourceJ12ScaledToCommon :
  ∀ {TimeIndex} (criterionData : SourceJ1CriterionData TimeIndex) →
  J12.pow3 (outputScale criterionData)
    * J12.sourceJ12Square (j12Data criterionData)
  ≤ (Int.+ 640 / 1) * J11.delta (j11Data criterionData)
sourceJ12ScaledToCommon criterionData =
  let
    j12 = j12Data criterionData
    raw = J12.sourceJ12CriterionScaling j12

    leftMeaning :
      J12.pow3 (J12.outputScale j12)
        * J12.sourceJ12Square j12
      ≡ J12.pow3 (outputScale criterionData)
        * J12.sourceJ12Square j12
    leftMeaning =
      cong
        (λ scale → J12.pow3 scale * J12.sourceJ12Square j12)
        (commonOutputScale criterionData)

    rightMeaning :
      (Int.+ 640 / 1) * J12.delta j12
      ≡ (Int.+ 640 / 1) * J11.delta (j11Data criterionData)
    rightMeaning =
      cong ((Int.+ 640 / 1) *_) (commonDelta criterionData)
  in
  subst₂ _≤_ leftMeaning rightMeaning raw

sourceJ1CriterionBound :
  ∀ {TimeIndex} (criterionData : SourceJ1CriterionData TimeIndex) →
  L2.square (sourceJ1 criterionData)
  ≤ (Int.+ 6400 / 1)
      * L2.square (J11.delta (j11Data criterionData))
sourceJ1CriterionBound criterionData =
  let
    j11 = j11Data criterionData
    j12 = j12Data criterionData
    q = outputScale criterionData
    delta = J11.delta j11
    j12Square = J12.sourceJ12Square j12

    j11Bound :
      J11.sourceJ11Squared j11
      ≤ (Int.+ 10 / 1) * delta * L2.square q
    j11Bound = J11.sourceJ11HalfRangeBound j11

    scaleByJ12 :
      J11.sourceJ11Squared j11 * j12Square
      ≤ ((Int.+ 10 / 1) * delta * L2.square q) * j12Square
    scaleByJ12 =
      let
        instance
          j12IsNonnegative =
            nonNegative (J12.sourceJ12SquareNonnegative j12)
      in
      ℚₚ.*-monoʳ-≤-nonNeg j12Square j11Bound

    squareJ12BelowCubeJ12 :
      L2.square q * j12Square
      ≤ J12.pow3 q * j12Square
    squareJ12BelowCubeJ12 =
      let
        instance
          j12IsNonnegative =
            nonNegative (J12.sourceJ12SquareNonnegative j12)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        j12Square (outputSquaredBelowCubed criterionData)

    coefficientNonnegative : 0ℚ ≤ (Int.+ 10 / 1) * delta
    coefficientNonnegative =
      nonnegativeProduct
        (toWitness {a? = 0ℚ ≤? (Int.+ 10 / 1)} _)
        (J11.deltaNonnegative j11)

    scaledCriterion :
      ((Int.+ 10 / 1) * delta)
        * (L2.square q * j12Square)
      ≤ ((Int.+ 10 / 1) * delta)
        * ((Int.+ 640 / 1) * delta)
    scaledCriterion =
      let
        instance
          coefficientIsNonnegative =
            nonNegative coefficientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        ((Int.+ 10 / 1) * delta)
        (ℚₚ.≤-trans
          squareJ12BelowCubeJ12
          (sourceJ12ScaledToCommon criterionData))

    reassociateLeft :
      ((Int.+ 10 / 1) * delta * L2.square q) * j12Square
      ≡ ((Int.+ 10 / 1) * delta)
          * (L2.square q * j12Square)
    reassociateLeft =
      solve (delta ∷ L2.square q ∷ j12Square ∷ [])

    targetMeaning :
      ((Int.+ 10 / 1) * delta)
        * ((Int.+ 640 / 1) * delta)
      ≡ (Int.+ 6400 / 1) * L2.square delta
    targetMeaning = solve (delta ∷ [])

    productBound :
      J11.sourceJ11Squared j11 * j12Square
      ≤ (Int.+ 6400 / 1) * L2.square delta
    productBound =
      ℚₚ.≤-trans scaleByJ12
        (subst
          (λ lower →
            lower ≤ (Int.+ 6400 / 1) * L2.square delta)
          (sym reassociateLeft)
          (subst
            (λ upper →
              ((Int.+ 10 / 1) * delta)
                * (L2.square q * j12Square)
              ≤ upper)
            targetMeaning
            scaledCriterion))
  in
  ℚₚ.≤-trans (sourceJ1Cauchy criterionData) productBound
