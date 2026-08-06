module DASHI.Physics.Closure.NSTriadKNLuoSourceJ12CriterionExact where

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
-- Derive the source J12 scaling from the exact five-shell overlap and the
-- localized high-frequency dissipation condition (4.6).  If
-- L=lambda_{q-2}, Q=lambda_q=4L, U is the unweighted five-shell time energy,
-- and W the corresponding lambda_r^2-weighted energy, then
--
--   L^2 U <= W,       L W <= 2 delta
--
-- imply L^3 U <= 2 delta.  Since J12^2<=5U and Q^3=64L^3,
--
--   Q^3 J12^2 <= 640 delta.
--
-- The estimate is square-safe and division-free.  No negative fractional
-- power or final J12 budget is supplied as a field.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact as Jensen
import DASHI.Physics.Closure.NSTriadKNLuoSourceJ12FiveShellExact as Five

pow2 pow3 : ℚ → ℚ
pow2 x = x * x
pow3 x = x * x * x

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

sumSquaresNonnegative :
  (values : List ℚ) → 0ℚ ≤ Jensen.sumSquares values
sumSquaresNonnegative [] = ℚₚ.≤-refl
sumSquaresNonnegative (value ∷ values) =
  L2.addNonnegative
    (L2.squareNonnegative value)
    (sumSquaresNonnegative values)

record SourceJ12CriterionData (Time : Set) : Set₁ where
  field
    window : Five.FiniteJ12FiveShellWindow Time
    outputScale lowerScale weightedTailIntegral delta : ℚ

    outputScaleNonnegative : 0ℚ ≤ outputScale
    lowerScaleNonnegative : 0ℚ ≤ lowerScale
    weightedTailIntegralNonnegative : 0ℚ ≤ weightedTailIntegral
    deltaNonnegative : 0ℚ ≤ delta

    oneBelowLowerScale : 1ℚ ≤ lowerScale
    outputScaleMeaning :
      outputScale ≡ (Int.+ 4 / 1) * lowerScale

    unweightedNearEnergyBelowWeightedTail :
      pow2 lowerScale * Five.nearEnergyIntegral window
      ≤ weightedTailIntegral

    localizedCriterionTailBound :
      lowerScale * weightedTailIntegral
      ≤ (Int.+ 2 / 1) * delta

open SourceJ12CriterionData public

nearEnergyNonnegative :
  ∀ {Time} (criterionData : SourceJ12CriterionData Time) →
  0ℚ ≤ Five.nearEnergyIntegral (window criterionData)
nearEnergyNonnegative {Time} criterionData =
  go (Five.times (window criterionData))
  where
  values = Five.amplitudes (window criterionData)
  weights = Five.timeWeight (window criterionData)

  nearSquareNonnegative :
    (time : Time) → 0ℚ ≤ Five.nearSquareSum (values time)
  nearSquareNonnegative time =
    sumSquaresNonnegative (Five.fiveShellValues (values time))

  go :
    (remaining : List Time) →
    0ℚ ≤ Five.weightedTimeSum remaining weights
      (λ time → Five.nearSquareSum (values time))
  go [] = ℚₚ.≤-refl
  go (time ∷ remaining) =
    L2.addNonnegative
      (nonnegativeProduct
        (Five.timeWeightNonnegative (window criterionData) time)
        (nearSquareNonnegative time))
      (go remaining)

lowerCubedNearEnergyBound :
  ∀ {Time} (criterionData : SourceJ12CriterionData Time) →
  pow3 (lowerScale criterionData)
    * Five.nearEnergyIntegral (window criterionData)
  ≤ (Int.+ 2 / 1) * delta criterionData
lowerCubedNearEnergyBound criterionData =
  let
    scaled :
      lowerScale criterionData
        * (pow2 (lowerScale criterionData)
            * Five.nearEnergyIntegral (window criterionData))
      ≤ lowerScale criterionData * weightedTailIntegral criterionData
    scaled =
      let
        instance
          lowerIsNonnegative =
            nonNegative (lowerScaleNonnegative criterionData)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (lowerScale criterionData)
        (unweightedNearEnergyBelowWeightedTail criterionData)

    leftMeaning :
      lowerScale criterionData
        * (pow2 (lowerScale criterionData)
            * Five.nearEnergyIntegral (window criterionData))
      ≡ pow3 (lowerScale criterionData)
          * Five.nearEnergyIntegral (window criterionData)
    leftMeaning =
      solve
        ( lowerScale criterionData
        ∷ Five.nearEnergyIntegral (window criterionData)
        ∷ []
        )
  in
  ℚₚ.≤-trans
    (subst
      (λ left →
        left
        ≤ lowerScale criterionData * weightedTailIntegral criterionData)
      leftMeaning
      scaled)
    (localizedCriterionTailBound criterionData)

sourceJ12Square :
  ∀ {Time} → SourceJ12CriterionData Time → ℚ
sourceJ12Square criterionData =
  Five.J12SquareIntegral (window criterionData)

sourceJ12SquareNonnegative :
  ∀ {Time} (criterionData : SourceJ12CriterionData Time) →
  0ℚ ≤ sourceJ12Square criterionData
sourceJ12SquareNonnegative {Time} criterionData =
  go (Five.times (window criterionData))
  where
  values = Five.amplitudes (window criterionData)
  weights = Five.timeWeight (window criterionData)

  go :
    (remaining : List Time) →
    0ℚ ≤ Five.weightedTimeSum remaining weights
      (λ time → L2.square (Five.nearSum (values time)))
  go [] = ℚₚ.≤-refl
  go (time ∷ remaining) =
    L2.addNonnegative
      (nonnegativeProduct
        (Five.timeWeightNonnegative (window criterionData) time)
        (L2.squareNonnegative (Five.nearSum (values time))))
      (go remaining)

sourceJ12CriterionScaling :
  ∀ {Time} (criterionData : SourceJ12CriterionData Time) →
  pow3 (outputScale criterionData) * sourceJ12Square criterionData
  ≤ (Int.+ 640 / 1) * delta criterionData
sourceJ12CriterionScaling criterionData =
  let
    j12ToNear :
      sourceJ12Square criterionData
      ≤ Five.five * Five.nearEnergyIntegral (window criterionData)
    j12ToNear = Five.sourceJ12FiveShellBound (window criterionData)

    outputCubeNonnegative : 0ℚ ≤ pow3 (outputScale criterionData)
    outputCubeNonnegative =
      nonnegativeProduct
        (nonnegativeProduct
          (outputScaleNonnegative criterionData)
          (outputScaleNonnegative criterionData))
        (outputScaleNonnegative criterionData)

    scaled :
      pow3 (outputScale criterionData) * sourceJ12Square criterionData
      ≤ pow3 (outputScale criterionData)
          * (Five.five * Five.nearEnergyIntegral (window criterionData))
    scaled =
      let
        instance
          cubeIsNonnegative = nonNegative outputCubeNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (pow3 (outputScale criterionData)) j12ToNear

    rewriteOutput :
      pow3 (outputScale criterionData)
        * (Five.five * Five.nearEnergyIntegral (window criterionData))
      ≡ (Int.+ 320 / 1)
          * (pow3 (lowerScale criterionData)
              * Five.nearEnergyIntegral (window criterionData))
    rewriteOutput
      rewrite outputScaleMeaning criterionData =
      solve
        ( lowerScale criterionData
        ∷ Five.nearEnergyIntegral (window criterionData)
        ∷ []
        )

    coefficientNonnegative : 0ℚ ≤ (Int.+ 320 / 1)
    coefficientNonnegative =
      toWitness {a? = 0ℚ ≤? (Int.+ 320 / 1)} _

    criterionScaled :
      (Int.+ 320 / 1)
        * (pow3 (lowerScale criterionData)
            * Five.nearEnergyIntegral (window criterionData))
      ≤ (Int.+ 320 / 1) * ((Int.+ 2 / 1) * delta criterionData)
    criterionScaled =
      let
        instance
          coefficientIsNonnegative =
            nonNegative coefficientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Int.+ 320 / 1)
        (lowerCubedNearEnergyBound criterionData)

    targetMeaning :
      (Int.+ 320 / 1) * ((Int.+ 2 / 1) * delta criterionData)
      ≡ (Int.+ 640 / 1) * delta criterionData
    targetMeaning = solve (delta criterionData ∷ [])
  in
  ℚₚ.≤-trans scaled
    (subst
      (λ lower → lower ≤ (Int.+ 640 / 1) * delta criterionData)
      rewriteOutput
      (subst
        (λ upper →
          (Int.+ 320 / 1)
            * (pow3 (lowerScale criterionData)
                * Five.nearEnergyIntegral (window criterionData))
          ≤ upper)
        targetMeaning
        criterionScaled))
