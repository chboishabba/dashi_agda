module DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionFilteredExact where

------------------------------------------------------------------------
-- S2b2d1b2 / PHYSICAL R236 FILTERED-LIST COVARIANCE DECOMPOSITION
--
-- Partition an arbitrary physical incidence list, preserving list order, into
--
--   DFL = deep far-low,
--   DHH = deep high-high,
--   C   = critical core.
--
-- Then the complete pair-difference covariance is EXACTLY
--
--   Cov(DFL)
-- + Bip(DFL,DHH)
-- + Bip(DFL,C)
-- + Cov(DHH)
-- + Bip(DHH,C)
-- + Cov(C).
--
-- Same-region terms inherit Pair.pairDifferenceClosedForm; cross-region terms
-- inherit the finite bipartite closed form.  This exposes only region
-- aggregates and never inserts an absolute value, norm, shell count or cutoff
-- cardinality estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFiniteBipartiteCovarianceExact as Bip
import DASHI.Physics.Closure.NSTriadKNPhysicalParabolicCriticalRegionRoutingExact as Region

deepFarLowItems :
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence
deepFarLowItems [] = []
deepFarLowItems (tau ∷ rest) with Region.criticalRegionTag tau
... | Region.deepFarLowRegion = tau ∷ deepFarLowItems rest
... | Region.deepHighHighRegion = deepFarLowItems rest
... | Region.criticalCoreRegion = deepFarLowItems rest

deepHighHighItems :
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence
deepHighHighItems [] = []
deepHighHighItems (tau ∷ rest) with Region.criticalRegionTag tau
... | Region.deepFarLowRegion = deepHighHighItems rest
... | Region.deepHighHighRegion = tau ∷ deepHighHighItems rest
... | Region.criticalCoreRegion = deepHighHighItems rest

criticalCoreItems :
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence
criticalCoreItems [] = []
criticalCoreItems (tau ∷ rest) with Region.criticalRegionTag tau
... | Region.deepFarLowRegion = criticalCoreItems rest
... | Region.deepHighHighRegion = criticalCoreItems rest
... | Region.criticalCoreRegion = tau ∷ criticalCoreItems rest

pairAgainstHeadRegionPartition :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (items : List Physical.PhysicalTriadIncidence) →
  Pair.pairAgainstHead rate work head items
  ≡
    Bip.bipartiteRow rate work head (deepFarLowItems items)
    + ( Bip.bipartiteRow rate work head (deepHighHighItems items)
      + Bip.bipartiteRow rate work head (criticalCoreItems items) )
pairAgainstHeadRegionPartition rate work head [] = solve []
pairAgainstHeadRegionPartition rate work head (tau ∷ rest)
  with Region.criticalRegionTag tau
... | Region.deepFarLowRegion
  rewrite pairAgainstHeadRegionPartition rate work head rest =
  solve
    ( (rate head - rate tau) * (work head - work tau)
    ∷ Bip.bipartiteRow rate work head (deepFarLowItems rest)
    ∷ Bip.bipartiteRow rate work head (deepHighHighItems rest)
    ∷ Bip.bipartiteRow rate work head (criticalCoreItems rest)
    ∷ [])
... | Region.deepHighHighRegion
  rewrite pairAgainstHeadRegionPartition rate work head rest =
  solve
    ( (rate head - rate tau) * (work head - work tau)
    ∷ Bip.bipartiteRow rate work head (deepFarLowItems rest)
    ∷ Bip.bipartiteRow rate work head (deepHighHighItems rest)
    ∷ Bip.bipartiteRow rate work head (criticalCoreItems rest)
    ∷ [])
... | Region.criticalCoreRegion
  rewrite pairAgainstHeadRegionPartition rate work head rest =
  solve
    ( (rate head - rate tau) * (work head - work tau)
    ∷ Bip.bipartiteRow rate work head (deepFarLowItems rest)
    ∷ Bip.bipartiteRow rate work head (deepHighHighItems rest)
    ∷ Bip.bipartiteRow rate work head (criticalCoreItems rest)
    ∷ [])

sixFilteredRegionCovariance :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
sixFilteredRegionCovariance rate work items =
    Pair.pairDifferenceWorkSum rate work (deepFarLowItems items)
  + Bip.bipartitePairSum rate work
      (deepFarLowItems items) (deepHighHighItems items)
  + Bip.bipartitePairSum rate work
      (deepFarLowItems items) (criticalCoreItems items)
  + Pair.pairDifferenceWorkSum rate work (deepHighHighItems items)
  + Bip.bipartitePairSum rate work
      (deepHighHighItems items) (criticalCoreItems items)
  + Pair.pairDifferenceWorkSum rate work (criticalCoreItems items)

pairDifferenceIsSixFilteredRegionCovariances :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Pair.pairDifferenceWorkSum rate work items
  ≡ sixFilteredRegionCovariance rate work items
pairDifferenceIsSixFilteredRegionCovariances rate work [] = solve []
pairDifferenceIsSixFilteredRegionCovariances rate work (head ∷ rest)
  with Region.criticalRegionTag head
... | Region.deepFarLowRegion
  rewrite pairAgainstHeadRegionPartition rate work head rest
        | pairDifferenceIsSixFilteredRegionCovariances rate work rest =
  solve
    ( Bip.bipartiteRow rate work head (deepFarLowItems rest)
    ∷ Bip.bipartiteRow rate work head (deepHighHighItems rest)
    ∷ Bip.bipartiteRow rate work head (criticalCoreItems rest)
    ∷ Pair.pairDifferenceWorkSum rate work (deepFarLowItems rest)
    ∷ Bip.bipartitePairSum rate work
        (deepFarLowItems rest) (deepHighHighItems rest)
    ∷ Bip.bipartitePairSum rate work
        (deepFarLowItems rest) (criticalCoreItems rest)
    ∷ Pair.pairDifferenceWorkSum rate work (deepHighHighItems rest)
    ∷ Bip.bipartitePairSum rate work
        (deepHighHighItems rest) (criticalCoreItems rest)
    ∷ Pair.pairDifferenceWorkSum rate work (criticalCoreItems rest)
    ∷ [])
... | Region.deepHighHighRegion
  rewrite pairAgainstHeadRegionPartition rate work head rest
        | pairDifferenceIsSixFilteredRegionCovariances rate work rest
        | Bip.bipartiteConsRight rate work
            (deepFarLowItems rest) head (deepHighHighItems rest) =
  solve
    ( Bip.bipartiteRow rate work head (deepFarLowItems rest)
    ∷ Bip.bipartiteRow rate work head (deepHighHighItems rest)
    ∷ Bip.bipartiteRow rate work head (criticalCoreItems rest)
    ∷ Pair.pairDifferenceWorkSum rate work (deepFarLowItems rest)
    ∷ Bip.bipartitePairSum rate work
        (deepFarLowItems rest) (deepHighHighItems rest)
    ∷ Bip.bipartitePairSum rate work
        (deepFarLowItems rest) (criticalCoreItems rest)
    ∷ Pair.pairDifferenceWorkSum rate work (deepHighHighItems rest)
    ∷ Bip.bipartitePairSum rate work
        (deepHighHighItems rest) (criticalCoreItems rest)
    ∷ Pair.pairDifferenceWorkSum rate work (criticalCoreItems rest)
    ∷ [])
... | Region.criticalCoreRegion
  rewrite pairAgainstHeadRegionPartition rate work head rest
        | pairDifferenceIsSixFilteredRegionCovariances rate work rest
        | Bip.bipartiteConsRight rate work
            (deepFarLowItems rest) head (criticalCoreItems rest)
        | Bip.bipartiteConsRight rate work
            (deepHighHighItems rest) head (criticalCoreItems rest) =
  solve
    ( Bip.bipartiteRow rate work head (deepFarLowItems rest)
    ∷ Bip.bipartiteRow rate work head (deepHighHighItems rest)
    ∷ Bip.bipartiteRow rate work head (criticalCoreItems rest)
    ∷ Pair.pairDifferenceWorkSum rate work (deepFarLowItems rest)
    ∷ Bip.bipartitePairSum rate work
        (deepFarLowItems rest) (deepHighHighItems rest)
    ∷ Bip.bipartitePairSum rate work
        (deepFarLowItems rest) (criticalCoreItems rest)
    ∷ Pair.pairDifferenceWorkSum rate work (deepHighHighItems rest)
    ∷ Bip.bipartitePairSum rate work
        (deepHighHighItems rest) (criticalCoreItems rest)
    ∷ Pair.pairDifferenceWorkSum rate work (criticalCoreItems rest)
    ∷ [])

------------------------------------------------------------------------
-- Named six physical-region blocks on filtered lists.
------------------------------------------------------------------------

deepFarLowCovariance :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
deepFarLowCovariance rate work items =
  Pair.pairDifferenceWorkSum rate work (deepFarLowItems items)

deepFarLowDeepHighHighCovariance :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
deepFarLowDeepHighHighCovariance rate work items =
  Bip.bipartitePairSum rate work
    (deepFarLowItems items) (deepHighHighItems items)

deepFarLowCoreCovariance :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
deepFarLowCoreCovariance rate work items =
  Bip.bipartitePairSum rate work
    (deepFarLowItems items) (criticalCoreItems items)

deepHighHighCovariance :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
deepHighHighCovariance rate work items =
  Pair.pairDifferenceWorkSum rate work (deepHighHighItems items)

deepHighHighCoreCovariance :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
deepHighHighCoreCovariance rate work items =
  Bip.bipartitePairSum rate work
    (deepHighHighItems items) (criticalCoreItems items)

criticalCoreCovariance :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
criticalCoreCovariance rate work items =
  Pair.pairDifferenceWorkSum rate work (criticalCoreItems items)

deepFarLowClosedForm :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  deepFarLowCovariance rate work items
  ≡
    Pair.natAsRational (Data.List.Base.length (deepFarLowItems items))
      * Pair.weightedWorkSum rate work (deepFarLowItems items)
    - Pair.rateSum rate (deepFarLowItems items)
      * Pair.workSum work (deepFarLowItems items)
deepFarLowClosedForm rate work items =
  Pair.pairDifferenceClosedForm rate work (deepFarLowItems items)

deepHighHighClosedForm :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  deepHighHighCovariance rate work items
  ≡
    Pair.natAsRational (Data.List.Base.length (deepHighHighItems items))
      * Pair.weightedWorkSum rate work (deepHighHighItems items)
    - Pair.rateSum rate (deepHighHighItems items)
      * Pair.workSum work (deepHighHighItems items)
deepHighHighClosedForm rate work items =
  Pair.pairDifferenceClosedForm rate work (deepHighHighItems items)

criticalCoreClosedForm :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  criticalCoreCovariance rate work items
  ≡
    Pair.natAsRational (Data.List.Base.length (criticalCoreItems items))
      * Pair.weightedWorkSum rate work (criticalCoreItems items)
    - Pair.rateSum rate (criticalCoreItems items)
      * Pair.workSum work (criticalCoreItems items)
criticalCoreClosedForm rate work items =
  Pair.pairDifferenceClosedForm rate work (criticalCoreItems items)

deepFarLowDeepHighHighClosedForm :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  deepFarLowDeepHighHighCovariance rate work items
  ≡
    Bip.bipartitePairSum rate work
      (deepFarLowItems items) (deepHighHighItems items)
deepFarLowDeepHighHighClosedForm rate work items = refl

filteredPhysicalCriticalRegionCovarianceDecompositionClosed : Bool
filteredPhysicalCriticalRegionCovarianceDecompositionClosed = true

filteredPhysicalRegionCovarianceUsesActualLists : Bool
filteredPhysicalRegionCovarianceUsesActualLists = true

filteredPhysicalRegionCovarianceIntroducesNorm : Bool
filteredPhysicalRegionCovarianceIntroducesNorm = false

filteredPhysicalRegionCovarianceIntroducesCardinalityEstimate : Bool
filteredPhysicalRegionCovarianceIntroducesCardinalityEstimate = false

clayPromotion : Bool
clayPromotion = false

filteredPhysicalCriticalRegionCovarianceDecompositionClosedIsTrue :
  filteredPhysicalCriticalRegionCovarianceDecompositionClosed ≡ true
filteredPhysicalCriticalRegionCovarianceDecompositionClosedIsTrue = refl
