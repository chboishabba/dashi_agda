module DASHI.Physics.Closure.NSTriadKNLuoSourceJ2CriterionExact where

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
-- Derive the J2 estimate (4.5)--(4.6) in square-safe rational form.  Put
-- L=lambda_{q-2}, Q=lambda_q=4L, let U be the unweighted high-tail time
-- integral and W its lambda_r^2-weighted counterpart.  From
--
--   L^2 U <= W,       L W <= 2 delta,
--
-- we prove L^3 U <= 2 delta and hence, for L>=1,
--
--   Q^5 U^2 <= 4096 delta^2 Q.
--
-- Since J2^2=Q^5U^2, this is exactly the source scaling delta^2 lambda_q.
-- No fractional power, division, or final J2 estimate is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (subst; subst₂; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

four thousandTwentyFour fourThousandNinetySix : ℚ
four = Int.+ 4 / 1
thousandTwentyFour = Int.+ 1024 / 1
fourThousandNinetySix = Int.+ 4096 / 1

fourNonnegative : 0ℚ ≤ four
fourNonnegative = toWitness {a? = 0ℚ ≤? four} _

oneBelowFour : 1ℚ ≤ four
oneBelowFour = toWitness {a? = 1ℚ ≤? four} _

thousandTwentyFourNonnegative : 0ℚ ≤ thousandTwentyFour
thousandTwentyFourNonnegative =
  toWitness {a? = 0ℚ ≤? thousandTwentyFour} _

fourThousandNinetySixNonnegative : 0ℚ ≤ fourThousandNinetySix
fourThousandNinetySixNonnegative =
  toWitness {a? = 0ℚ ≤? fourThousandNinetySix} _

pow2 pow3 pow5 pow6 : ℚ → ℚ
pow2 x = x * x
pow3 x = x * x * x
pow5 x = x * x * x * x * x
pow6 x = pow3 x * pow3 x

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

pow3Nonnegative : ∀ {x} → 0ℚ ≤ x → 0ℚ ≤ pow3 x
pow3Nonnegative {x} xNonnegative =
  nonnegativeProduct
    (nonnegativeProduct xNonnegative xNonnegative)
    xNonnegative

pow5Nonnegative : ∀ {x} → 0ℚ ≤ x → 0ℚ ≤ pow5 x
pow5Nonnegative {x} xNonnegative =
  nonnegativeProduct
    (nonnegativeProduct
      (nonnegativeProduct
        (nonnegativeProduct xNonnegative xNonnegative)
        xNonnegative)
      xNonnegative)
    xNonnegative

squareMonotoneNonnegative :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → left ≤ right →
  L2.square left ≤ L2.square right
squareMonotoneNonnegative {left} {right} leftNonnegative leftBelowRight =
  let
    rightNonnegative : 0ℚ ≤ right
    rightNonnegative = ℚₚ.≤-trans leftNonnegative leftBelowRight

    first : left * left ≤ right * left
    first =
      let
        instance
          leftIsNonnegative = nonNegative leftNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg left leftBelowRight

    second : right * left ≤ right * right
    second =
      let
        instance
          rightIsNonnegative = nonNegative rightNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg right leftBelowRight
  in
  ℚₚ.≤-trans first second

record SourceJ2CriterionData : Set where
  field
    outputScale lowerScale : ℚ
    tailIntegral weightedTailIntegral delta : ℚ

    lowerScaleNonnegative : 0ℚ ≤ lowerScale
    tailIntegralNonnegative : 0ℚ ≤ tailIntegral
    weightedTailIntegralNonnegative : 0ℚ ≤ weightedTailIntegral
    deltaNonnegative : 0ℚ ≤ delta

    oneBelowLowerScale : 1ℚ ≤ lowerScale
    outputScaleMeaning : outputScale ≡ four * lowerScale

    unweightedTailBelowWeightedTail :
      pow2 lowerScale * tailIntegral ≤ weightedTailIntegral

    localizedCriterionTailBound :
      lowerScale * weightedTailIntegral
      ≤ (Int.+ 2 / 1) * delta

open SourceJ2CriterionData public

lowerCubedTailBound :
  (criterionData : SourceJ2CriterionData) →
  pow3 (lowerScale criterionData) * tailIntegral criterionData
  ≤ (Int.+ 2 / 1) * delta criterionData
lowerCubedTailBound criterionData =
  let
    raw :
      lowerScale criterionData
        * (pow2 (lowerScale criterionData) * tailIntegral criterionData)
      ≤ lowerScale criterionData * weightedTailIntegral criterionData
    raw =
      let
        instance
          lowerIsNonnegative =
            nonNegative (lowerScaleNonnegative criterionData)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (lowerScale criterionData)
        (unweightedTailBelowWeightedTail criterionData)

    leftMeaning :
      lowerScale criterionData
        * (pow2 (lowerScale criterionData) * tailIntegral criterionData)
      ≡ pow3 (lowerScale criterionData) * tailIntegral criterionData
    leftMeaning =
      solve
        (lowerScale criterionData ∷ tailIntegral criterionData ∷ [])
  in
  ℚₚ.≤-trans
    (subst
      (λ left →
        left
        ≤ lowerScale criterionData * weightedTailIntegral criterionData)
      leftMeaning
      raw)
    (localizedCriterionTailBound criterionData)

lowerSixthTailSquareBound :
  (criterionData : SourceJ2CriterionData) →
  pow6 (lowerScale criterionData)
    * L2.square (tailIntegral criterionData)
  ≤ four * L2.square (delta criterionData)
lowerSixthTailSquareBound criterionData =
  let
    left = pow3 (lowerScale criterionData) * tailIntegral criterionData
    right = (Int.+ 2 / 1) * delta criterionData

    leftNonnegative : 0ℚ ≤ left
    leftNonnegative =
      nonnegativeProduct
        (pow3Nonnegative (lowerScaleNonnegative criterionData))
        (tailIntegralNonnegative criterionData)

    squared =
      squareMonotoneNonnegative
        leftNonnegative
        (lowerCubedTailBound criterionData)

    leftMeaning :
      L2.square left
      ≡ pow6 (lowerScale criterionData)
          * L2.square (tailIntegral criterionData)
    leftMeaning =
      solve
        (lowerScale criterionData ∷ tailIntegral criterionData ∷ [])

    rightMeaning :
      L2.square right ≡ four * L2.square (delta criterionData)
    rightMeaning = solve (delta criterionData ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning squared

lowerFifthTailBelowSixth :
  (criterionData : SourceJ2CriterionData) →
  pow5 (lowerScale criterionData)
    * L2.square (tailIntegral criterionData)
  ≤ pow6 (lowerScale criterionData)
      * L2.square (tailIntegral criterionData)
lowerFifthTailBelowSixth criterionData =
  let
    common =
      pow5 (lowerScale criterionData)
      * L2.square (tailIntegral criterionData)

    commonNonnegative : 0ℚ ≤ common
    commonNonnegative =
      nonnegativeProduct
        (pow5Nonnegative (lowerScaleNonnegative criterionData))
        (L2.squareNonnegative (tailIntegral criterionData))

    raw : common * 1ℚ ≤ common * lowerScale criterionData
    raw =
      let
        instance
          commonIsNonnegative = nonNegative commonNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        common (oneBelowLowerScale criterionData)

    leftMeaning : common * 1ℚ ≡ common
    leftMeaning = solve (common ∷ [])

    rightMeaning :
      common * lowerScale criterionData
      ≡ pow6 (lowerScale criterionData)
          * L2.square (tailIntegral criterionData)
    rightMeaning =
      solve
        (lowerScale criterionData ∷ tailIntegral criterionData ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning raw

outputScaleAtLeastOne :
  (criterionData : SourceJ2CriterionData) →
  1ℚ ≤ outputScale criterionData
outputScaleAtLeastOne criterionData =
  let
    lower = lowerScale criterionData

    raw : 1ℚ * lower ≤ four * lower
    raw =
      let
        instance
          lowerIsNonnegative =
            nonNegative (lowerScaleNonnegative criterionData)
      in
      ℚₚ.*-monoʳ-≤-nonNeg lower oneBelowFour

    leftMeaning : 1ℚ * lower ≡ lower
    leftMeaning = solve (lower ∷ [])

    lowerBelowOutputExpression : lower ≤ four * lower
    lowerBelowOutputExpression =
      subst
        (λ left → left ≤ four * lower)
        leftMeaning
        raw

    oneBelowOutputExpression : 1ℚ ≤ four * lower
    oneBelowOutputExpression =
      ℚₚ.≤-trans
        (oneBelowLowerScale criterionData)
        lowerBelowOutputExpression
  in
  subst
    (λ right → 1ℚ ≤ right)
    (sym (outputScaleMeaning criterionData))
    oneBelowOutputExpression

sourceJ2Square : SourceJ2CriterionData → ℚ
sourceJ2Square criterionData =
  pow5 (outputScale criterionData)
  * L2.square (tailIntegral criterionData)

sourceJ2CriterionSquareBound :
  (criterionData : SourceJ2CriterionData) →
  sourceJ2Square criterionData
  ≤ fourThousandNinetySix
      * L2.square (delta criterionData)
      * outputScale criterionData
sourceJ2CriterionSquareBound criterionData =
  let
    lowerFive =
      pow5 (lowerScale criterionData)
      * L2.square (tailIntegral criterionData)
    lowerSix =
      pow6 (lowerScale criterionData)
      * L2.square (tailIntegral criterionData)

    lowerBound : lowerFive ≤ four * L2.square (delta criterionData)
    lowerBound =
      ℚₚ.≤-trans
        (lowerFifthTailBelowSixth criterionData)
        (lowerSixthTailSquareBound criterionData)

    scaledLower :
      thousandTwentyFour * lowerFive
      ≤ thousandTwentyFour * (four * L2.square (delta criterionData))
    scaledLower =
      let
        instance
          constantIsNonnegative =
            nonNegative thousandTwentyFourNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg thousandTwentyFour lowerBound

    sourceMeaning :
      sourceJ2Square criterionData
      ≡ thousandTwentyFour * lowerFive
    sourceMeaning
      rewrite outputScaleMeaning criterionData =
      solve
        (lowerScale criterionData ∷ tailIntegral criterionData ∷ [])

    constantMeaning :
      thousandTwentyFour * (four * L2.square (delta criterionData))
      ≡ fourThousandNinetySix * L2.square (delta criterionData)
    constantMeaning = solve (delta criterionData ∷ [])

    baseBound :
      sourceJ2Square criterionData
      ≤ fourThousandNinetySix * L2.square (delta criterionData)
    baseBound =
      subst₂ _≤_
        (sym sourceMeaning)
        constantMeaning
        scaledLower

    coefficient =
      fourThousandNinetySix * L2.square (delta criterionData)

    coefficientNonnegative : 0ℚ ≤ coefficient
    coefficientNonnegative =
      nonnegativeProduct
        fourThousandNinetySixNonnegative
        (L2.squareNonnegative (delta criterionData))

    rawOutput :
      coefficient * 1ℚ ≤ coefficient * outputScale criterionData
    rawOutput =
      let
        instance
          coefficientIsNonnegative =
            nonNegative coefficientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        coefficient
        (outputScaleAtLeastOne criterionData)

    leftIdentity : coefficient * 1ℚ ≡ coefficient
    leftIdentity = solve (coefficient ∷ [])

    scaleByOutput :
      coefficient ≤ coefficient * outputScale criterionData
    scaleByOutput =
      subst
        (λ left → left ≤ coefficient * outputScale criterionData)
        leftIdentity
        rawOutput
  in
  ℚₚ.≤-trans baseBound scaleByOutput
