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
-- Compose the derived source estimates for J11 and J12 with the weighted
-- time-window Cauchy theorem.  The physical identification fields below only
-- state that the two Cauchy factors are the concrete J11 and J12 quantities;
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

open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
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

record SourceJ1CriterionData (Time : Set) : Set₁ where
  field
    j11Data : J11.SourceJ11HalfRangeData Time
    j12Data : J12.SourceJ12CriterionData Time
    j1Window : Product.FiniteSourceJ1Window Time

    j11FactorMeaning :
      Product.J11Squared j1Window
      ≡ J11.sourceJ11Squared j11Data

    j12FactorMeaning :
      Product.J12Squared j1Window
      ≡ J12.sourceJ12Square j12Data

    commonOutputScale :
      J12.outputScale j12Data
      ≡ J11.Source.lambda (J11.outputShell j11Data)

    commonDelta :
      J12.delta j12Data ≡ J11.delta j11Data

open SourceJ1CriterionData public

outputScale : ∀ {Time} → SourceJ1CriterionData Time → ℚ
outputScale data = J11.Source.lambda (J11.outputShell (j11Data data))

sourceJ1 : ∀ {Time} → SourceJ1CriterionData Time → ℚ
sourceJ1 data = Product.J1 (j1Window data)

outputScaleNonnegative :
  ∀ {Time} (data : SourceJ1CriterionData Time) →
  0ℚ ≤ outputScale data
outputScaleNonnegative data =
  J11.Prefix.powTwoNonnegative (J11.outputShell (j11Data data))

outputScaleAtLeastOne :
  ∀ {Time} (data : SourceJ1CriterionData Time) →
  1ℚ ≤ outputScale data
outputScaleAtLeastOne data =
  let
    j12 = j12Data data

    lowerBelowFourLower :
      J12.lowerScale j12
      ≤ (Int.+ 4 / 1) * J12.lowerScale j12
    lowerBelowFourLower =
      let instance lowerIsNonnegative =
        nonNegative (J12.lowerScaleNonnegative j12)
      in
      subst
        (λ right → J12.lowerScale j12 ≤ right)
        (solve (J12.lowerScale j12 ∷ []))
        (ℚₚ.*-monoʳ-≤-nonNeg
          (J12.lowerScale j12)
          oneBelowFour)

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
    (commonOutputScale data)
    oneBelowJ12Output

sourceJ11SquareNonnegative :
  ∀ {Time} (data : SourceJ1CriterionData Time) →
  0ℚ ≤ J11.sourceJ11Squared (j11Data data)
sourceJ11SquareNonnegative data = go (J11.times (j11Data data))
  where
  j11 = j11Data data

  go :
    (remaining : _) →
    0ℚ ≤ J11.Time.weightedTimeSum
      remaining
      (J11.timeWeight j11)
      (λ time →
        L2.square
          (J11.Sum.sumTo
            (J11.Source.sourceAmplitude
              (J11.normalizedAmplitude j11 time))
            (J11.outputShell j11)))
  go [] = ℚₚ.≤-refl
  go (time ∷ remaining) =
    J11.L2.addNonnegative
      (nonnegativeProduct
        (J11.timeWeightNonnegative j11 time)
        (L2.squareNonnegative
          (J11.Sum.sumTo
            (J11.Source.sourceAmplitude
              (J11.normalizedAmplitude j11 time))
            (J11.outputShell j11))))
      (go remaining)

sourceJ1Cauchy :
  ∀ {Time} (data : SourceJ1CriterionData Time) →
  L2.square (sourceJ1 data)
  ≤ J11.sourceJ11Squared (j11Data data)
      * J12.sourceJ12Square (j12Data data)
sourceJ1Cauchy data =
  subst
    (λ upper → L2.square (sourceJ1 data) ≤ upper)
    (cong₂ _*_
      (j11FactorMeaning data)
      (j12FactorMeaning data))
    (Product.J1SquareBelowJ11J12 (j1Window data))

outputSquaredBelowCubed :
  ∀ {Time} (data : SourceJ1CriterionData Time) →
  L2.square (outputScale data)
  ≤ J12.pow3 (outputScale data)
outputSquaredBelowCubed data =
  let
    squareNonnegative = L2.squareNonnegative (outputScale data)
    scaled :
      L2.square (outputScale data) * 1ℚ
      ≤ L2.square (outputScale data) * outputScale data
    scaled =
      let instance squareIsNonnegative = nonNegative squareNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (L2.square (outputScale data))
        (outputScaleAtLeastOne data)
  in
  subst
    (λ left → left ≤ J12.pow3 (outputScale data))
    (solve (L2.square (outputScale data) ∷ []))
    (subst
      (λ right →
        L2.square (outputScale data) * 1ℚ ≤ right)
      (solve (outputScale data ∷ []))
      scaled)

sourceJ12ScaledToCommon :
  ∀ {Time} (data : SourceJ1CriterionData Time) →
  J12.pow3 (outputScale data)
    * J12.sourceJ12Square (j12Data data)
  ≤ (Int.+ 640 / 1) * J11.delta (j11Data data)
sourceJ12ScaledToCommon data =
  subst
    (λ upper →
      J12.pow3 (outputScale data)
        * J12.sourceJ12Square (j12Data data)
      ≤ upper)
    (cong ((Int.+ 640 / 1) *_) (commonDelta data))
    (subst
      (λ left →
        left * J12.sourceJ12Square (j12Data data)
        ≤ (Int.+ 640 / 1) * J12.delta (j12Data data))
      (cong J12.pow3 (commonOutputScale data))
      (J12.sourceJ12CriterionScaling (j12Data data)))

sourceJ1CriterionBound :
  ∀ {Time} (data : SourceJ1CriterionData Time) →
  L2.square (sourceJ1 data)
  ≤ (Int.+ 6400 / 1) * L2.square (J11.delta (j11Data data))
sourceJ1CriterionBound data =
  let
    j11 = j11Data data
    j12 = j12Data data
    q = outputScale data
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
      let instance j12IsNonnegative =
        nonNegative (J12.sourceJ12SquareNonnegative j12)
      in
      ℚₚ.*-monoʳ-≤-nonNeg j12Square j11Bound

    squareJ12BelowCubeJ12 :
      L2.square q * j12Square
      ≤ J12.pow3 q * j12Square
    squareJ12BelowCubeJ12 =
      let instance j12IsNonnegative =
        nonNegative (J12.sourceJ12SquareNonnegative j12)
      in
      ℚₚ.*-monoʳ-≤-nonNeg j12Square (outputSquaredBelowCubed data)

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
      let instance coefficientIsNonnegative =
        nonNegative coefficientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        ((Int.+ 10 / 1) * delta)
        (ℚₚ.≤-trans
          squareJ12BelowCubeJ12
          (sourceJ12ScaledToCommon data))

    reassociateLeft :
      ((Int.+ 10 / 1) * delta * L2.square q) * j12Square
      ≡ ((Int.+ 10 / 1) * delta)
          * (L2.square q * j12Square)
    reassociateLeft = solve (delta ∷ L2.square q ∷ j12Square ∷ [])

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
  ℚₚ.≤-trans (sourceJ1Cauchy data) productBound
