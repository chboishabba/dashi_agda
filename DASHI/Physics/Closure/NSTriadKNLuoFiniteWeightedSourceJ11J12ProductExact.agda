module DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedSourceJ11J12ProductExact where

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
-- Compose the weighted time-window J11 and J12 estimates with the exact
-- Section-4 product theorem.  The lower/upper J11 split and weighted Jensen
-- estimates are derived upstream; this module only asks that their explicit
-- budgets fit the intended physical upper and lower weights.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedJensenExact as Jensen
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact as Half
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedSourceSection4Exact as Source
import DASHI.Physics.Closure.NSTriadKNLuoSection4ProductClosureExact as Product

weightedJ11 : Source.WeightedSourceSection4Data → ℚ
weightedJ11 data =
  Jensen.firstMoment (Source.j11LowerSamples data)
  + Jensen.firstMoment (Source.j11UpperSamples data)

weightedJ12 : Source.WeightedSourceSection4Data → ℚ
weightedJ12 data = Jensen.firstMoment (Source.j12Samples data)

weightedJ11Budget : Source.WeightedSourceSection4Data → ℚ
weightedJ11Budget data =
  Half.two
  * ( Jensen.mass (Source.j11LowerSamples data)
      * Source.j11LowerEnergy data
    + Jensen.mass (Source.j11UpperSamples data)
      * Source.j11UpperEnergy data)

weightedJ12Budget : Source.WeightedSourceSection4Data → ℚ
weightedJ12Budget data =
  Jensen.mass (Source.j12Samples data) * Source.j12Energy data

record WeightedSourceProductData : Set where
  constructor weighted-source-product
  field
    source : Source.WeightedSourceSection4Data

    delta upperWeight lowerWeight targetWeight : ℚ

    deltaNonnegative : 0ℚ ≤ delta
    deltaAtMostOne : delta ≤ 1ℚ
    upperWeightNonnegative : 0ℚ ≤ upperWeight
    lowerWeightNonnegative : 0ℚ ≤ lowerWeight
    targetWeightNonnegative : 0ℚ ≤ targetWeight

    j11BudgetFitsPhysicalWeight :
      weightedJ11Budget source ≤ delta * upperWeight

    j12BudgetFitsPhysicalWeight :
      weightedJ12Budget source ≤ delta * lowerWeight

    weightProductBound :
      upperWeight * lowerWeight ≤ targetWeight

open WeightedSourceProductData public

weightedJ11SquaredPhysicalBound :
  (data : WeightedSourceProductData) →
  L2.square (weightedJ11 (source data))
  ≤ delta data * upperWeight data
weightedJ11SquaredPhysicalBound data =
  ℚₚ.≤-trans
    (Source.j11WeightedSourceBound (source data))
    (j11BudgetFitsPhysicalWeight data)

weightedJ12SquaredPhysicalBound :
  (data : WeightedSourceProductData) →
  L2.square (weightedJ12 (source data))
  ≤ delta data * lowerWeight data
weightedJ12SquaredPhysicalBound data =
  ℚₚ.≤-trans
    (Source.j12WeightedSourceBound (source data))
    (j12BudgetFitsPhysicalWeight data)

asSection4ProductData :
  WeightedSourceProductData → Product.Section4ProductData
asSection4ProductData data =
  Product.section4-product
    (weightedJ11 (source data))
    (weightedJ12 (source data))
    (delta data)
    (upperWeight data)
    (lowerWeight data)
    (targetWeight data)
    (deltaNonnegative data)
    (deltaAtMostOne data)
    (upperWeightNonnegative data)
    (lowerWeightNonnegative data)
    (targetWeightNonnegative data)
    (weightedJ11SquaredPhysicalBound data)
    (weightedJ12SquaredPhysicalBound data)
    (weightProductBound data)

weightedSourceProductSquaredBound :
  (data : WeightedSourceProductData) →
  Product.square
    (weightedJ11 (source data) * weightedJ12 (source data))
  ≤ Product.square (delta data)
      * (upperWeight data * lowerWeight data)
weightedSourceProductSquaredBound data =
  Product.section4ProductSquaredBound
    (asSection4ProductData data)

weightedSourceJ1TargetBound :
  (data : WeightedSourceProductData) →
  Product.square
    (weightedJ11 (source data) * weightedJ12 (source data))
  ≤ delta data * targetWeight data
weightedSourceJ1TargetBound data =
  Product.section4J1SquaredBound
    (asSection4ProductData data)

finiteWeightedSourceProductClosed : Bool
finiteWeightedSourceProductClosed = true

finiteWeightedSourceProductClosedIsTrue :
  finiteWeightedSourceProductClosed ≡ true
finiteWeightedSourceProductClosedIsTrue = refl
