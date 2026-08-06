module DASHI.Physics.Closure.NSTriadKNLuoSourceJ12FiveShellExact where

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
-- Prove the exact finite-overlap estimate for the source factor
--
--   sum_{|r-q|<=2} ||u_r||_2.
--
-- There are exactly five slots.  Finite Cauchy gives the pointwise square
-- bound by five times the sum of the five squared amplitudes, and monotone
-- weighted summation transports the same constant through an arbitrary
-- nonnegative time window.  The J12 estimate is derived rather than stored.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact as Jensen

five : ℚ
five = Int.+ 5 / 1

record FiveShellAmplitude : Set where
  constructor five-shell
  field
    minusTwo minusOne center plusOne plusTwo : ℚ

open FiveShellAmplitude public

fiveShellValues : FiveShellAmplitude → List ℚ
fiveShellValues values =
  minusTwo values
  ∷ minusOne values
  ∷ center values
  ∷ plusOne values
  ∷ plusTwo values
  ∷ []

nearSum : FiveShellAmplitude → ℚ
nearSum values = Jensen.sumValues (fiveShellValues values)

nearSquareSum : FiveShellAmplitude → ℚ
nearSquareSum values = Jensen.sumSquares (fiveShellValues values)

fiveShellLength :
  (values : FiveShellAmplitude) →
  Jensen.rationalLength (fiveShellValues values) ≡ five
fiveShellLength values = refl

fiveShellPointwiseSquareBound :
  (values : FiveShellAmplitude) →
  L2.square (nearSum values) ≤ five * nearSquareSum values
fiveShellPointwiseSquareBound values =
  let
    raw = Jensen.finiteJensenSquare (fiveShellValues values)

    rightMeaning :
      nearSquareSum values
        * Jensen.rationalLength (fiveShellValues values)
      ≡ five * nearSquareSum values
    rightMeaning
      rewrite fiveShellLength values =
      solve (nearSquareSum values ∷ five ∷ [])
  in
  subst
    (λ upper → L2.square (nearSum values) ≤ upper)
    rightMeaning
    raw

weightedTimeSum :
  ∀ {Time : Set} →
  List Time → (Time → ℚ) → (Time → ℚ) → ℚ
weightedTimeSum [] weight value = 0ℚ
weightedTimeSum (time ∷ times) weight value =
  weight time * value time + weightedTimeSum times weight value

weightedTimeSumMonotone :
  ∀ {Time : Set}
    (times : List Time)
    (weight lower upper : Time → ℚ) →
  ((time : Time) → 0ℚ ≤ weight time) →
  ((time : Time) → lower time ≤ upper time) →
  weightedTimeSum times weight lower
  ≤ weightedTimeSum times weight upper
weightedTimeSumMonotone [] weight lower upper weightNonnegative pointwise =
  ℚₚ.≤-refl
weightedTimeSumMonotone
  (time ∷ times) weight lower upper weightNonnegative pointwise =
  ℚₚ.+-mono-≤
    (let instance timeWeightIsNonnegative =
       nonNegative (weightNonnegative time)
     in
     ℚₚ.*-monoˡ-≤-nonNeg (weight time) (pointwise time))
    (weightedTimeSumMonotone
      times weight lower upper weightNonnegative pointwise)

weightedTimeSumFiveScale :
  ∀ {Time : Set}
    (times : List Time)
    (weight value : Time → ℚ) →
  weightedTimeSum times weight (λ time → five * value time)
  ≡ five * weightedTimeSum times weight value
weightedTimeSumFiveScale [] weight value = solve (five ∷ [])
weightedTimeSumFiveScale (time ∷ times) weight value
  rewrite weightedTimeSumFiveScale times weight value =
  solve
    ( five
    ∷ weight time
    ∷ value time
    ∷ weightedTimeSum times weight value
    ∷ []
    )

record FiniteJ12FiveShellWindow (Time : Set) : Set where
  field
    times : List Time
    timeWeight : Time → ℚ
    amplitudes : Time → FiveShellAmplitude
    timeWeightNonnegative :
      (time : Time) → 0ℚ ≤ timeWeight time

open FiniteJ12FiveShellWindow public

J12SquareIntegral :
  ∀ {Time} → FiniteJ12FiveShellWindow Time → ℚ
J12SquareIntegral data =
  weightedTimeSum
    (times data)
    (timeWeight data)
    (λ time → L2.square (nearSum (amplitudes data time)))

nearEnergyIntegral :
  ∀ {Time} → FiniteJ12FiveShellWindow Time → ℚ
nearEnergyIntegral data =
  weightedTimeSum
    (times data)
    (timeWeight data)
    (λ time → nearSquareSum (amplitudes data time))

sourceJ12FiveShellBound :
  ∀ {Time} (data : FiniteJ12FiveShellWindow Time) →
  J12SquareIntegral data ≤ five * nearEnergyIntegral data
sourceJ12FiveShellBound data =
  let
    pointwise :
      J12SquareIntegral data
      ≤ weightedTimeSum
          (times data)
          (timeWeight data)
          (λ time → five * nearSquareSum (amplitudes data time))
    pointwise =
      weightedTimeSumMonotone
        (times data)
        (timeWeight data)
        (λ time → L2.square (nearSum (amplitudes data time)))
        (λ time → five * nearSquareSum (amplitudes data time))
        (timeWeightNonnegative data)
        (λ time → fiveShellPointwiseSquareBound (amplitudes data time))
  in
  subst
    (λ upper → J12SquareIntegral data ≤ upper)
    (weightedTimeSumFiveScale
      (times data)
      (timeWeight data)
      (λ time → nearSquareSum (amplitudes data time)))
    pointwise
