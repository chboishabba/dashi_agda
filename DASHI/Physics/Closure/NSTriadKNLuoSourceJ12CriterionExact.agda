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
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
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
  ∀ {Time} (data : SourceJ12CriterionData Time) →
  0ℚ ≤ Five.nearEnergyIntegral (window data)
nearEnergyNonnegative {Time} data = go (Five.times (window data))
  where
  values = Five.amplitudes (window data)
  weights = Five.timeWeight (window data)

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
        (Five.timeWeightNonnegative (window data) time)
        (nearSquareNonnegative time))
      (go remaining)

lowerCubedNearEnergyBound :
  ∀ {Time} (data : SourceJ12CriterionData Time) →
  pow3 (lowerScale data)
    * Five.nearEnergyIntegral (window data)
  ≤ (Int.+ 2 / 1) * delta data
lowerCubedNearEnergyBound data =
  let
    scaled :
      lowerScale data
        * (pow2 (lowerScale data)
            * Five.nearEnergyIntegral (window data))
      ≤ lowerScale data * weightedTailIntegral data
    scaled =
      let instance lowerIsNonnegative =
        nonNegative (lowerScaleNonnegative data)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (lowerScale data)
        (unweightedNearEnergyBelowWeightedTail data)

    leftMeaning :
      lowerScale data
        * (pow2 (lowerScale data)
            * Five.nearEnergyIntegral (window data))
      ≡ pow3 (lowerScale data)
          * Five.nearEnergyIntegral (window data)
    leftMeaning =
      solve
        ( lowerScale data
        ∷ Five.nearEnergyIntegral (window data)
        ∷ []
        )
  in
  ℚₚ.≤-trans
    (subst
      (λ left → left ≤ lowerScale data * weightedTailIntegral data)
      leftMeaning
      scaled)
    (localizedCriterionTailBound data)

sourceJ12Square :
  ∀ {Time} → SourceJ12CriterionData Time → ℚ
sourceJ12Square data = Five.J12SquareIntegral (window data)

sourceJ12SquareNonnegative :
  ∀ {Time} (data : SourceJ12CriterionData Time) →
  0ℚ ≤ sourceJ12Square data
sourceJ12SquareNonnegative {Time} data = go (Five.times (window data))
  where
  values = Five.amplitudes (window data)
  weights = Five.timeWeight (window data)

  go :
    (remaining : List Time) →
    0ℚ ≤ Five.weightedTimeSum remaining weights
      (λ time → L2.square (Five.nearSum (values time)))
  go [] = ℚₚ.≤-refl
  go (time ∷ remaining) =
    L2.addNonnegative
      (nonnegativeProduct
        (Five.timeWeightNonnegative (window data) time)
        (L2.squareNonnegative (Five.nearSum (values time))))
      (go remaining)

sourceJ12CriterionScaling :
  ∀ {Time} (data : SourceJ12CriterionData Time) →
  pow3 (outputScale data) * sourceJ12Square data
  ≤ (Int.+ 640 / 1) * delta data
sourceJ12CriterionScaling data =
  let
    j12ToNear :
      sourceJ12Square data
      ≤ Five.five * Five.nearEnergyIntegral (window data)
    j12ToNear = Five.sourceJ12FiveShellBound (window data)

    outputCubeNonnegative : 0ℚ ≤ pow3 (outputScale data)
    outputCubeNonnegative =
      nonnegativeProduct
        (nonnegativeProduct
          (outputScaleNonnegative data)
          (outputScaleNonnegative data))
        (outputScaleNonnegative data)

    scaled :
      pow3 (outputScale data) * sourceJ12Square data
      ≤ pow3 (outputScale data)
          * (Five.five * Five.nearEnergyIntegral (window data))
    scaled =
      let instance cubeIsNonnegative = nonNegative outputCubeNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg (pow3 (outputScale data)) j12ToNear

    rewriteOutput :
      pow3 (outputScale data)
        * (Five.five * Five.nearEnergyIntegral (window data))
      ≡ (Int.+ 320 / 1)
          * (pow3 (lowerScale data)
              * Five.nearEnergyIntegral (window data))
    rewriteOutput
      rewrite outputScaleMeaning data =
      solve
        ( lowerScale data
        ∷ Five.nearEnergyIntegral (window data)
        ∷ []
        )

    coefficientNonnegative : 0ℚ ≤ (Int.+ 320 / 1)
    coefficientNonnegative =
      toWitness {a? = 0ℚ ≤? (Int.+ 320 / 1)} _

    criterionScaled :
      (Int.+ 320 / 1)
        * (pow3 (lowerScale data)
            * Five.nearEnergyIntegral (window data))
      ≤ (Int.+ 320 / 1) * ((Int.+ 2 / 1) * delta data)
    criterionScaled =
      let instance coefficientIsNonnegative =
        nonNegative coefficientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Int.+ 320 / 1)
        (lowerCubedNearEnergyBound data)

    targetMeaning :
      (Int.+ 320 / 1) * ((Int.+ 2 / 1) * delta data)
      ≡ (Int.+ 640 / 1) * delta data
    targetMeaning = solve (delta data ∷ [])
  in
  ℚₚ.≤-trans scaled
    (subst
      (λ lower → lower ≤ (Int.+ 640 / 1) * delta data)
      rewriteOutput
      (subst
        (λ upper →
          (Int.+ 320 / 1)
            * (pow3 (lowerScale data)
                * Five.nearEnergyIntegral (window data))
          ≤ upper)
        targetMeaning
        criterionScaled))
