module DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedSourceSection4Exact where

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
-- Strengthen the finite source-faithful Section-4 lane from equal samples to
-- arbitrary nonnegative rational time weights.  Each component estimate is
-- obtained from the exact weighted Jensen defect theorem and a separately
-- proved weighted square budget.  The J11 lower/upper split is then recombined
-- by the exact two-range inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedJensenExact as Jensen
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact as Half

record WeightedSourceSection4Data : Set where
  constructor weighted-source-section4
  field
    j11LowerSamples j11UpperSamples j12Samples j2Samples :
      List Jensen.WeightedValue

    j11LowerEnergy j11UpperEnergy j12Energy j2Energy : ℚ

    j11LowerSecondMomentBound :
      Jensen.secondMoment j11LowerSamples ≤ j11LowerEnergy

    j11UpperSecondMomentBound :
      Jensen.secondMoment j11UpperSamples ≤ j11UpperEnergy

    j12SecondMomentBound :
      Jensen.secondMoment j12Samples ≤ j12Energy

    j2SecondMomentBound :
      Jensen.secondMoment j2Samples ≤ j2Energy

open WeightedSourceSection4Data public

massNonnegative :
  (samples : List Jensen.WeightedValue) →
  0ℚ ≤ Jensen.mass samples
massNonnegative [] = ℚₚ.≤-refl
massNonnegative (sample ∷ samples) =
  L2.addNonnegative
    (Jensen.weightNonnegative sample)
    (massNonnegative samples)

weightedJensenWithEnergyBudget :
  (samples : List Jensen.WeightedValue) →
  (energy : ℚ) →
  Jensen.secondMoment samples ≤ energy →
  L2.square (Jensen.firstMoment samples)
  ≤ Jensen.mass samples * energy
weightedJensenWithEnergyBudget samples energy momentBound =
  ℚₚ.≤-trans
    (Jensen.finiteWeightedJensenSquare samples)
    (let instance massIsNonnegative = nonNegative (massNonnegative samples)
     in
     ℚₚ.*-monoˡ-≤-nonNeg
       (Jensen.mass samples)
       momentBound)

j11LowerWeightedSourceBound :
  (data : WeightedSourceSection4Data) →
  L2.square (Jensen.firstMoment (j11LowerSamples data))
  ≤ Jensen.mass (j11LowerSamples data) * j11LowerEnergy data
j11LowerWeightedSourceBound data =
  weightedJensenWithEnergyBudget
    (j11LowerSamples data)
    (j11LowerEnergy data)
    (j11LowerSecondMomentBound data)

j11UpperWeightedSourceBound :
  (data : WeightedSourceSection4Data) →
  L2.square (Jensen.firstMoment (j11UpperSamples data))
  ≤ Jensen.mass (j11UpperSamples data) * j11UpperEnergy data
j11UpperWeightedSourceBound data =
  weightedJensenWithEnergyBudget
    (j11UpperSamples data)
    (j11UpperEnergy data)
    (j11UpperSecondMomentBound data)

j12WeightedSourceBound :
  (data : WeightedSourceSection4Data) →
  L2.square (Jensen.firstMoment (j12Samples data))
  ≤ Jensen.mass (j12Samples data) * j12Energy data
j12WeightedSourceBound data =
  weightedJensenWithEnergyBudget
    (j12Samples data)
    (j12Energy data)
    (j12SecondMomentBound data)

j2WeightedSourceBound :
  (data : WeightedSourceSection4Data) →
  L2.square (Jensen.firstMoment (j2Samples data))
  ≤ Jensen.mass (j2Samples data) * j2Energy data
j2WeightedSourceBound data =
  weightedJensenWithEnergyBudget
    (j2Samples data)
    (j2Energy data)
    (j2SecondMomentBound data)

j11WeightedSourceBound :
  (data : WeightedSourceSection4Data) →
  L2.square
    ( Jensen.firstMoment (j11LowerSamples data)
    + Jensen.firstMoment (j11UpperSamples data))
  ≤ Half.two
    * ( Jensen.mass (j11LowerSamples data) * j11LowerEnergy data
      + Jensen.mass (j11UpperSamples data) * j11UpperEnergy data)
j11WeightedSourceBound data =
  let
    split = Half.squareOfSumBelowTwiceSquares
      (Jensen.firstMoment (j11LowerSamples data))
      (Jensen.firstMoment (j11UpperSamples data))

    components :
      L2.square (Jensen.firstMoment (j11LowerSamples data))
        + L2.square (Jensen.firstMoment (j11UpperSamples data))
      ≤ Jensen.mass (j11LowerSamples data) * j11LowerEnergy data
        + Jensen.mass (j11UpperSamples data) * j11UpperEnergy data
    components =
      ℚₚ.+-mono-≤
        (j11LowerWeightedSourceBound data)
        (j11UpperWeightedSourceBound data)

    scaled :
      Half.two
        * ( L2.square (Jensen.firstMoment (j11LowerSamples data))
          + L2.square (Jensen.firstMoment (j11UpperSamples data)))
      ≤ Half.two
        * ( Jensen.mass (j11LowerSamples data) * j11LowerEnergy data
          + Jensen.mass (j11UpperSamples data) * j11UpperEnergy data)
    scaled =
      let instance twoIsNonnegative = nonNegative Half.twoNonnegative
      in ℚₚ.*-monoˡ-≤-nonNeg Half.two components
  in
  ℚₚ.≤-trans split scaled

finiteWeightedSourceJ11Closed : Bool
finiteWeightedSourceJ11Closed = true

finiteWeightedSourceJ12J2Closed : Bool
finiteWeightedSourceJ12J2Closed = true

finiteWeightedSourceJ11ClosedIsTrue :
  finiteWeightedSourceJ11Closed ≡ true
finiteWeightedSourceJ11ClosedIsTrue = refl

finiteWeightedSourceJ12J2ClosedIsTrue :
  finiteWeightedSourceJ12J2Closed ≡ true
finiteWeightedSourceJ12J2ClosedIsTrue = refl
