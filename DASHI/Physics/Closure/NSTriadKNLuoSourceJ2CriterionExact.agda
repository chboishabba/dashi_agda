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
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
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
      let instance leftIsNonnegative = nonNegative leftNonnegative
      in ℚₚ.*-monoʳ-≤-nonNeg left leftBelowRight

    second : right * left ≤ right * right
    second =
      let instance rightIsNonnegative = nonNegative rightNonnegative
      in ℚₚ.*-monoˡ-≤-nonNeg right leftBelowRight
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
  (data : SourceJ2CriterionData) →
  pow3 (lowerScale data) * tailIntegral data
  ≤ (Int.+ 2 / 1) * delta data
lowerCubedTailBound data =
  let
    raw :
      lowerScale data
        * (pow2 (lowerScale data) * tailIntegral data)
      ≤ lowerScale data * weightedTailIntegral data
    raw =
      let instance lowerIsNonnegative =
        nonNegative (lowerScaleNonnegative data)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (lowerScale data)
        (unweightedTailBelowWeightedTail data)

    leftMeaning :
      lowerScale data
        * (pow2 (lowerScale data) * tailIntegral data)
      ≡ pow3 (lowerScale data) * tailIntegral data
    leftMeaning = solve (lowerScale data ∷ tailIntegral data ∷ [])
  in
  ℚₚ.≤-trans
    (subst
      (λ left → left ≤ lowerScale data * weightedTailIntegral data)
      leftMeaning
      raw)
    (localizedCriterionTailBound data)

lowerSixthTailSquareBound :
  (data : SourceJ2CriterionData) →
  pow6 (lowerScale data) * L2.square (tailIntegral data)
  ≤ four * L2.square (delta data)
lowerSixthTailSquareBound data =
  let
    left = pow3 (lowerScale data) * tailIntegral data
    right = (Int.+ 2 / 1) * delta data

    leftNonnegative : 0ℚ ≤ left
    leftNonnegative =
      nonnegativeProduct
        (pow3Nonnegative (lowerScaleNonnegative data))
        (tailIntegralNonnegative data)

    squared =
      squareMonotoneNonnegative
        leftNonnegative
        (lowerCubedTailBound data)

    leftMeaning :
      L2.square left
      ≡ pow6 (lowerScale data) * L2.square (tailIntegral data)
    leftMeaning = solve (lowerScale data ∷ tailIntegral data ∷ [])

    rightMeaning :
      L2.square right ≡ four * L2.square (delta data)
    rightMeaning = solve (delta data ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning squared

lowerFifthTailBelowSixth :
  (data : SourceJ2CriterionData) →
  pow5 (lowerScale data) * L2.square (tailIntegral data)
  ≤ pow6 (lowerScale data) * L2.square (tailIntegral data)
lowerFifthTailBelowSixth data =
  let
    common = pow5 (lowerScale data) * L2.square (tailIntegral data)

    commonNonnegative : 0ℚ ≤ common
    commonNonnegative =
      nonnegativeProduct
        (pow5Nonnegative (lowerScaleNonnegative data))
        (L2.squareNonnegative (tailIntegral data))

    raw : common * 1ℚ ≤ common * lowerScale data
    raw =
      let instance commonIsNonnegative = nonNegative commonNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg common (oneBelowLowerScale data)

    leftMeaning : common * 1ℚ ≡ common
    leftMeaning = solve (common ∷ [])

    rightMeaning :
      common * lowerScale data
      ≡ pow6 (lowerScale data) * L2.square (tailIntegral data)
    rightMeaning = solve (lowerScale data ∷ tailIntegral data ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning raw

outputScaleAtLeastOne :
  (data : SourceJ2CriterionData) → 1ℚ ≤ outputScale data
outputScaleAtLeastOne data =
  let
    lower = lowerScale data

    raw : 1ℚ * lower ≤ four * lower
    raw =
      let instance lowerIsNonnegative =
        nonNegative (lowerScaleNonnegative data)
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
        (oneBelowLowerScale data)
        lowerBelowOutputExpression
  in
  subst
    (λ right → 1ℚ ≤ right)
    (sym (outputScaleMeaning data))
    oneBelowOutputExpression

sourceJ2Square : SourceJ2CriterionData → ℚ
sourceJ2Square data =
  pow5 (outputScale data) * L2.square (tailIntegral data)

sourceJ2CriterionSquareBound :
  (data : SourceJ2CriterionData) →
  sourceJ2Square data
  ≤ fourThousandNinetySix
      * L2.square (delta data) * outputScale data
sourceJ2CriterionSquareBound data =
  let
    lowerFive =
      pow5 (lowerScale data) * L2.square (tailIntegral data)
    lowerSix =
      pow6 (lowerScale data) * L2.square (tailIntegral data)

    lowerBound : lowerFive ≤ four * L2.square (delta data)
    lowerBound =
      ℚₚ.≤-trans
        (lowerFifthTailBelowSixth data)
        (lowerSixthTailSquareBound data)

    scaledLower :
      thousandTwentyFour * lowerFive
      ≤ thousandTwentyFour * (four * L2.square (delta data))
    scaledLower =
      let instance constantIsNonnegative =
        nonNegative thousandTwentyFourNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg thousandTwentyFour lowerBound

    sourceMeaning :
      sourceJ2Square data ≡ thousandTwentyFour * lowerFive
    sourceMeaning
      rewrite outputScaleMeaning data =
      solve (lowerScale data ∷ tailIntegral data ∷ [])

    constantMeaning :
      thousandTwentyFour * (four * L2.square (delta data))
      ≡ fourThousandNinetySix * L2.square (delta data)
    constantMeaning = solve (delta data ∷ [])

    baseBound :
      sourceJ2Square data
      ≤ fourThousandNinetySix * L2.square (delta data)
    baseBound =
      subst₂ _≤_
        (sym sourceMeaning)
        constantMeaning
        scaledLower

    coefficient = fourThousandNinetySix * L2.square (delta data)

    coefficientNonnegative : 0ℚ ≤ coefficient
    coefficientNonnegative =
      nonnegativeProduct
        fourThousandNinetySixNonnegative
        (L2.squareNonnegative (delta data))

    rawOutput : coefficient * 1ℚ ≤ coefficient * outputScale data
    rawOutput =
      let instance coefficientIsNonnegative =
        nonNegative coefficientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        coefficient
        (outputScaleAtLeastOne data)

    leftIdentity : coefficient * 1ℚ ≡ coefficient
    leftIdentity = solve (coefficient ∷ [])

    scaleByOutput : coefficient ≤ coefficient * outputScale data
    scaleByOutput =
      subst
        (λ left → left ≤ coefficient * outputScale data)
        leftIdentity
        rawOutput
  in
  ℚₚ.≤-trans baseBound scaleByOutput
