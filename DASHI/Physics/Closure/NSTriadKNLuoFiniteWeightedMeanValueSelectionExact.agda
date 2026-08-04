module DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedMeanValueSelectionExact where

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
-- Prove the weighted finite mean-value selection needed for nonuniform time
-- partitions.  The minimum of the sampled values is constructed by the
-- existing total-order selector.  Nonnegative weights then imply the exact
-- division-free estimate
--
--   selected * sum_i w_i <= sum_i w_i a_i.
--
-- The selected value is proved to occur in the window and to lie below every
-- sample; it is not supplied as an external witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteMeanValueSelectionExact as Mean
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedJensenExact as Weighted

sampleValues : List Weighted.WeightedValue → List ℚ
sampleValues [] = []
sampleValues (sample ∷ samples) =
  Weighted.value sample ∷ sampleValues samples

lowerTimesMassBelowMoment :
  (lower : ℚ) →
  (samples : List Weighted.WeightedValue) →
  ((candidate : ℚ) →
    Mean.Occurs candidate (sampleValues samples) →
    lower ≤ candidate) →
  lower * Weighted.mass samples ≤ Weighted.firstMoment samples
lowerTimesMassBelowMoment lower [] lowerBound = ℚₚ.≤-refl
lowerTimesMassBelowMoment lower (sample ∷ samples) lowerBound =
  let
    headBound : lower ≤ Weighted.value sample
    headBound = lowerBound (Weighted.value sample) Mean.here

    weightedHeadBound :
      Weighted.weight sample * lower
      ≤ Weighted.weight sample * Weighted.value sample
    weightedHeadBound =
      let instance weightIsNonnegative =
        nonNegative (Weighted.weightNonnegative sample)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Weighted.weight sample)
        headBound

    tailBound :
      lower * Weighted.mass samples
      ≤ Weighted.firstMoment samples
    tailBound =
      lowerTimesMassBelowMoment
        lower
        samples
        (λ candidate occurrence →
          lowerBound candidate (Mean.there occurrence))

    combined :
      Weighted.weight sample * lower
        + lower * Weighted.mass samples
      ≤ Weighted.weight sample * Weighted.value sample
        + Weighted.firstMoment samples
    combined = ℚₚ.+-mono-≤ weightedHeadBound tailBound

    leftMeaning :
      lower * Weighted.mass (sample ∷ samples)
      ≡ Weighted.weight sample * lower
        + lower * Weighted.mass samples
    leftMeaning =
      solve
        ( lower
        ∷ Weighted.weight sample
        ∷ Weighted.mass samples
        ∷ []
        )
  in
  subst
    (λ left →
      left
      ≤ Weighted.weight sample * Weighted.value sample
        + Weighted.firstMoment samples)
    (symmetry leftMeaning)
    combined
  where
  symmetry : ∀ {left right : ℚ} → left ≡ right → right ≡ left
  symmetry refl = refl

record WeightedMeanValueSelection
    (samples : List Weighted.WeightedValue) : Set where
  constructor weighted-mean-value
  field
    selected : ℚ
    selectedOccurs : Mean.Occurs selected (sampleValues samples)
    selectedBelowEvery :
      (candidate : ℚ) →
      Mean.Occurs candidate (sampleValues samples) →
      selected ≤ candidate
    selectedTimesMassBelowMoment :
      selected * Weighted.mass samples
      ≤ Weighted.firstMoment samples

open WeightedMeanValueSelection public

finiteWeightedMeanValueSelection :
  (head : Weighted.WeightedValue) →
  (tail : List Weighted.WeightedValue) →
  WeightedMeanValueSelection (head ∷ tail)
finiteWeightedMeanValueSelection head tail =
  let
    minimum = Mean.selectMinimum
      (Weighted.value head)
      (sampleValues tail)
  in
  weighted-mean-value
    (Mean.value minimum)
    (Mean.occurs minimum)
    (Mean.belowEvery minimum)
    (lowerTimesMassBelowMoment
      (Mean.value minimum)
      (head ∷ tail)
      (Mean.belowEvery minimum))

finiteWeightedMeanValueSelectionClosed : Bool
finiteWeightedMeanValueSelectionClosed = true

finiteWeightedMeanValueSelectionClosedIsTrue :
  finiteWeightedMeanValueSelectionClosed ≡ true
finiteWeightedMeanValueSelectionClosedIsTrue = refl
