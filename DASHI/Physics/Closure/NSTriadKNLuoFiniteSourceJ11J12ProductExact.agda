module DASHI.Physics.Closure.NSTriadKNLuoFiniteSourceJ11J12ProductExact where

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
-- Feed the source-faithful finite J11/J12 estimates into the exact Section-4
-- product theorem.  The J11 square estimate comes from the lower/upper dyadic
-- split plus Jensen; the J12 estimate comes from its own sample-square budget.
-- Only the comparison of those derived budgets with the intended physical
-- weights remains an input.  The product estimate itself is derived.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact as Jensen
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact as Half
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSourceFaithfulSection4Exact as Source
import DASHI.Physics.Closure.NSTriadKNLuoSection4ProductClosureExact as Product

sourceJ11 : Source.FiniteSourceFaithfulSection4Data → ℚ
sourceJ11 data =
  Jensen.sumValues (Source.j11LowerSamples data)
  + Jensen.sumValues (Source.j11UpperSamples data)

sourceJ12 : Source.FiniteSourceFaithfulSection4Data → ℚ
sourceJ12 data = Jensen.sumValues (Source.j12Samples data)

sourceJ11Budget : Source.FiniteSourceFaithfulSection4Data → ℚ
sourceJ11Budget data =
  Half.two
  * ( Jensen.rationalLength (Source.j11LowerSamples data)
      * Source.j11LowerEnergy data
    + Jensen.rationalLength (Source.j11UpperSamples data)
      * Source.j11UpperEnergy data
    )

sourceJ12Budget : Source.FiniteSourceFaithfulSection4Data → ℚ
sourceJ12Budget data =
  Jensen.rationalLength (Source.j12Samples data)
  * Source.j12Energy data

record FiniteSourceProductData : Set where
  constructor finite-source-product
  field
    source : Source.FiniteSourceFaithfulSection4Data

    delta upperWeight lowerWeight targetWeight : ℚ

    deltaNonnegative : 0ℚ ≤ delta
    deltaAtMostOne : delta ≤ 1ℚ
    upperWeightNonnegative : 0ℚ ≤ upperWeight
    lowerWeightNonnegative : 0ℚ ≤ lowerWeight
    targetWeightNonnegative : 0ℚ ≤ targetWeight

    sourceJ11BudgetComparison :
      sourceJ11Budget source ≤ delta * upperWeight

    sourceJ12BudgetComparison :
      sourceJ12Budget source ≤ delta * lowerWeight

    weightProductBound :
      upperWeight * lowerWeight ≤ targetWeight

open FiniteSourceProductData public

sourceJ11SquaredBound :
  (data : FiniteSourceProductData) →
  L2.square (sourceJ11 (source data))
  ≤ delta data * upperWeight data
sourceJ11SquaredBound data =
  ℚₚ.≤-trans
    (Source.j11SourceBound (source data))
    (sourceJ11BudgetComparison data)

sourceJ12SquaredBound :
  (data : FiniteSourceProductData) →
  L2.square (sourceJ12 (source data))
  ≤ delta data * lowerWeight data
sourceJ12SquaredBound data =
  ℚₚ.≤-trans
    (Source.j12SourceBound (source data))
    (sourceJ12BudgetComparison data)

asSection4ProductData :
  FiniteSourceProductData → Product.Section4ProductData
asSection4ProductData data =
  Product.section4-product
    (sourceJ11 (source data))
    (sourceJ12 (source data))
    (delta data)
    (upperWeight data)
    (lowerWeight data)
    (targetWeight data)
    (deltaNonnegative data)
    (deltaAtMostOne data)
    (upperWeightNonnegative data)
    (lowerWeightNonnegative data)
    (targetWeightNonnegative data)
    (sourceJ11SquaredBound data)
    (sourceJ12SquaredBound data)
    (weightProductBound data)

sourceJ11J12ProductSquaredBound :
  (data : FiniteSourceProductData) →
  Product.square
    (sourceJ11 (source data) * sourceJ12 (source data))
  ≤ Product.square (delta data)
      * (upperWeight data * lowerWeight data)
sourceJ11J12ProductSquaredBound data =
  Product.section4ProductSquaredBound
    (asSection4ProductData data)

sourceJ1TargetSquaredBound :
  (data : FiniteSourceProductData) →
  Product.square
    (sourceJ11 (source data) * sourceJ12 (source data))
  ≤ delta data * targetWeight data
sourceJ1TargetSquaredBound data =
  Product.section4J1SquaredBound
    (asSection4ProductData data)

finiteSourceJ11J12ProductClosed : Bool
finiteSourceJ11J12ProductClosed = true

finiteSourceJ1TargetClosed : Bool
finiteSourceJ1TargetClosed = true

finiteSourceJ11J12ProductClosedIsTrue :
  finiteSourceJ11J12ProductClosed ≡ true
finiteSourceJ11J12ProductClosedIsTrue = refl

finiteSourceJ1TargetClosedIsTrue :
  finiteSourceJ1TargetClosed ≡ true
finiteSourceJ1TargetClosedIsTrue = refl
