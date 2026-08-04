module DASHI.Physics.Closure.NSTriadKNLuoFiniteIndexedSourceJ1Exact where

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
-- Complete the finite source-faithful chain from one indexed J11 shell list,
-- through the literal 2r<=q split and Jensen estimates, to the Section-4 J1
-- product bound.  Only the comparisons of the explicit lower/upper budgets
-- with the intended physical weights remain assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact as Jensen
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHalfShellPartitionExact as Partition
import DASHI.Physics.Closure.NSTriadKNLuoFiniteIndexedSourceSection4Exact as Indexed
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSourceJ11J12ProductExact as SourceProduct
import DASHI.Physics.Closure.NSTriadKNLuoSection4ProductClosureExact as Product

record IndexedSourceJ1Data : Set where
  constructor indexed-source-j1
  field
    source : Indexed.IndexedSourceSection4Data

    delta upperWeight lowerWeight targetWeight : ℚ

    deltaNonnegative : 0ℚ ≤ delta
    deltaAtMostOne : delta ≤ 1ℚ
    upperWeightNonnegative : 0ℚ ≤ upperWeight
    lowerWeightNonnegative : 0ℚ ≤ lowerWeight
    targetWeightNonnegative : 0ℚ ≤ targetWeight

    j11BudgetFitsPhysicalWeight :
      SourceProduct.sourceJ11Budget (Indexed.asSourceData source)
      ≤ delta * upperWeight

    j12BudgetFitsPhysicalWeight :
      SourceProduct.sourceJ12Budget (Indexed.asSourceData source)
      ≤ delta * lowerWeight

    weightProductBound :
      upperWeight * lowerWeight ≤ targetWeight

open IndexedSourceJ1Data public

asSourceProductData :
  IndexedSourceJ1Data → SourceProduct.FiniteSourceProductData
asSourceProductData data =
  SourceProduct.finite-source-product
    (Indexed.asSourceData (source data))
    (delta data)
    (upperWeight data)
    (lowerWeight data)
    (targetWeight data)
    (deltaNonnegative data)
    (deltaAtMostOne data)
    (upperWeightNonnegative data)
    (lowerWeightNonnegative data)
    (targetWeightNonnegative data)
    (j11BudgetFitsPhysicalWeight data)
    (j12BudgetFitsPhysicalWeight data)
    (weightProductBound data)

indexedJ1 : IndexedSourceJ1Data → ℚ
indexedJ1 data =
  Partition.sumOriginal (Indexed.j11IndexedSamples (source data))
  * Jensen.sumValues (Indexed.j12Samples (source data))

indexedJ1Meaning :
  (data : IndexedSourceJ1Data) →
  indexedJ1 data
  ≡ SourceProduct.sourceJ11
      (Indexed.asSourceData (source data))
    * SourceProduct.sourceJ12
      (Indexed.asSourceData (source data))
indexedJ1Meaning data =
  cong
    (λ j11 →
      j11 * SourceProduct.sourceJ12
        (Indexed.asSourceData (source data)))
    (Indexed.indexedJ11FoldMeaning (source data))

indexedSourceJ1TargetBound :
  (data : IndexedSourceJ1Data) →
  Product.square (indexedJ1 data)
  ≤ delta data * targetWeight data
indexedSourceJ1TargetBound data =
  subst
    (λ j1Value →
      Product.square j1Value ≤ delta data * targetWeight data)
    (symmetry (indexedJ1Meaning data))
    (SourceProduct.sourceJ1TargetSquaredBound
      (asSourceProductData data))
  where
  symmetry : ∀ {left right : ℚ} → left ≡ right → right ≡ left
  symmetry refl = refl

finiteIndexedSourceJ1Closed : Bool
finiteIndexedSourceJ1Closed = true

finiteIndexedSourceJ1ClosedIsTrue :
  finiteIndexedSourceJ1Closed ≡ true
finiteIndexedSourceJ1ClosedIsTrue = refl
