module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectBipartite20261007Exact where

------------------------------------------------------------------------
-- POSITIVE B4 / CORE-NONCORE DEFECT -> EXACT BIPARTITE COVARIANCE NORMAL FORM
--
-- After the principal Core-Core half-margin is closed, B4 has one remaining
-- signed scalar: the Core-noncore defect.  Do not replace it by an absolute
-- majorant.  The existing R236 filtered-list owner already knows the exact
-- DFL/Core and DHH/Core bipartite covariance objects.
--
-- This owner proves on the SAME physical pair graph
--
--   defect
--     = - [ Bip(DFL,Core) + Bip(DHH,Core) ]
--
-- and then rewrites each bipartite term by the existing four-aggregate closed
-- form.  Thus pair enumeration is removed from the final B4 research seam;
-- no estimate, norm, shell count, or cutoff-cardinality bound is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalParabolicCriticalRegionRoutingExact as Routing
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFiniteBipartiteCovarianceExact as Bip
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact as Blocks
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionFilteredExact as Filtered
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Exact as SplitRows
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive

F : C3.RealField _
F = Rational.rationalRealField

positiveDefectBlock : Blocks.RegionPairBlocks → ℚ
positiveDefectBlock blocks =
  Blocks.deepFarLowCriticalCore blocks
  + Blocks.deepHighHighCriticalCore blocks

positiveDefectBlocksAdd :
  (left right : Blocks.RegionPairBlocks) →
  positiveDefectBlock (Blocks.addBlocks left right)
  ≡ positiveDefectBlock left + positiveDefectBlock right
positiveDefectBlocksAdd
  (Blocks.region-pair-blocks
    (Blocks.region-row a b c) (Blocks.region-row d e f) (Blocks.region-row g h i))
  (Blocks.region-pair-blocks
    (Blocks.region-row j k l) (Blocks.region-row m n o) (Blocks.region-row p q r)) =
  solve (c ∷ f ∷ g ∷ h ∷ l ∷ o ∷ p ∷ q ∷ [])

defectCovariance :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
defectCovariance rate work items =
  Filtered.deepFarLowCoreCovariance rate work items
  + Filtered.deepHighHighCoreCovariance rate work items

defectAgainstFiltered :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
defectAgainstFiltered rate work head rest
  with Routing.criticalRegionTag head
... | Routing.deepFarLowRegion =
  Bip.bipartiteRow rate work head (Filtered.criticalCoreItems rest)
... | Routing.deepHighHighRegion =
  Bip.bipartiteRow rate work head (Filtered.criticalCoreItems rest)
... | Routing.criticalCoreRegion =
  Bip.bipartiteRow rate work head (Filtered.deepFarLowItems rest)
  + Bip.bipartiteRow rate work head (Filtered.deepHighHighItems rest)

positiveDefectRouteMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  positiveDefectBlock
    (Blocks.routePair alpha beta (Blocks.pairTerm rate work alpha beta))
  ≡
  let term = Blocks.pairTerm rate work alpha beta
  in
  case Routing.criticalRegionTag alpha of λ where
    Routing.deepFarLowRegion →
      case Routing.criticalRegionTag beta of λ where
        Routing.criticalCoreRegion → term
        _ → 0ℚ
    Routing.deepHighHighRegion →
      case Routing.criticalRegionTag beta of λ where
        Routing.criticalCoreRegion → term
        _ → 0ℚ
    Routing.criticalCoreRegion →
      case Routing.criticalRegionTag beta of λ where
        Routing.deepFarLowRegion → term
        Routing.deepHighHighRegion → term
        Routing.criticalCoreRegion → 0ℚ
positiveDefectRouteMeaning rate work alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = solve []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = solve []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = solve []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = solve []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = solve []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = solve []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = solve []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = solve []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = solve []

positiveDefectAgainstHeadMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  positiveDefectBlock (Blocks.blocksAgainstHead rate work head rest)
  ≡ defectAgainstFiltered rate work head rest
positiveDefectAgainstHeadMeaning rate work head []
  with Routing.criticalRegionTag head
... | Routing.deepFarLowRegion = solve []
... | Routing.deepHighHighRegion = solve []
... | Routing.criticalCoreRegion = solve []
positiveDefectAgainstHeadMeaning rate work head (x ∷ xs)
  with Routing.criticalRegionTag head | Routing.criticalRegionTag x
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.routePair head x (Blocks.pairTerm rate work head x))
            (Blocks.blocksAgainstHead rate work head xs)
        | positiveDefectAgainstHeadMeaning rate work head xs = solve []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.routePair head x (Blocks.pairTerm rate work head x))
            (Blocks.blocksAgainstHead rate work head xs)
        | positiveDefectAgainstHeadMeaning rate work head xs = solve []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.routePair head x (Blocks.pairTerm rate work head x))
            (Blocks.blocksAgainstHead rate work head xs)
        | positiveDefectAgainstHeadMeaning rate work head xs = solve []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.routePair head x (Blocks.pairTerm rate work head x))
            (Blocks.blocksAgainstHead rate work head xs)
        | positiveDefectAgainstHeadMeaning rate work head xs = solve []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.routePair head x (Blocks.pairTerm rate work head x))
            (Blocks.blocksAgainstHead rate work head xs)
        | positiveDefectAgainstHeadMeaning rate work head xs = solve []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.routePair head x (Blocks.pairTerm rate work head x))
            (Blocks.blocksAgainstHead rate work head xs)
        | positiveDefectAgainstHeadMeaning rate work head xs = solve []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.routePair head x (Blocks.pairTerm rate work head x))
            (Blocks.blocksAgainstHead rate work head xs)
        | positiveDefectAgainstHeadMeaning rate work head xs = solve []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.routePair head x (Blocks.pairTerm rate work head x))
            (Blocks.blocksAgainstHead rate work head xs)
        | positiveDefectAgainstHeadMeaning rate work head xs = solve []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.routePair head x (Blocks.pairTerm rate work head x))
            (Blocks.blocksAgainstHead rate work head xs)
        | positiveDefectAgainstHeadMeaning rate work head xs = solve []

positiveDefectPairBlocksMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  positiveDefectBlock (Blocks.pairBlocks rate work items)
  ≡ defectCovariance rate work items
positiveDefectPairBlocksMeaning rate work [] = solve []
positiveDefectPairBlocksMeaning rate work (head ∷ rest)
  with Routing.criticalRegionTag head
... | Routing.deepFarLowRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.blocksAgainstHead rate work head rest)
            (Blocks.pairBlocks rate work rest)
        | positiveDefectAgainstHeadMeaning rate work head rest
        | positiveDefectPairBlocksMeaning rate work rest = solve []
... | Routing.deepHighHighRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.blocksAgainstHead rate work head rest)
            (Blocks.pairBlocks rate work rest)
        | positiveDefectAgainstHeadMeaning rate work head rest
        | positiveDefectPairBlocksMeaning rate work rest = solve []
... | Routing.criticalCoreRegion
  rewrite positiveDefectBlocksAdd
            (Blocks.blocksAgainstHead rate work head rest)
            (Blocks.pairBlocks rate work rest)
        | positiveDefectAgainstHeadMeaning rate work head rest
        | positiveDefectPairBlocksMeaning rate work rest
        | Bip.bipartiteConsRight rate work
            (Filtered.deepFarLowItems rest) head (Filtered.criticalCoreItems rest)
        | Bip.bipartiteConsRight rate work
            (Filtered.deepHighHighItems rest) head (Filtered.criticalCoreItems rest) = solve []

splitDefectBlockIsNegativePositiveDefect :
  (blocks : Blocks.RegionPairBlocks) →
  SplitRows.defectBlock blocks ≡ 0ℚ - positiveDefectBlock blocks
splitDefectBlockIsNegativePositiveDefect blocks =
  solve
    ( Blocks.deepFarLowCriticalCore blocks
    ∷ Blocks.deepHighHighCriticalCore blocks
    ∷ [])

------------------------------------------------------------------------
-- Four-aggregate normal form of the two bipartite terms.
------------------------------------------------------------------------

defectAggregateNormalForm :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
defectAggregateNormalForm rate work items =
    Pair.natAsRational (length (Filtered.criticalCoreItems items))
      * Pair.weightedWorkSum rate work (Filtered.deepFarLowItems items)
  + Pair.natAsRational (length (Filtered.deepFarLowItems items))
      * Pair.weightedWorkSum rate work (Filtered.criticalCoreItems items)
  - Pair.rateSum rate (Filtered.deepFarLowItems items)
      * Pair.workSum work (Filtered.criticalCoreItems items)
  - Pair.rateSum rate (Filtered.criticalCoreItems items)
      * Pair.workSum work (Filtered.deepFarLowItems items)
  + Pair.natAsRational (length (Filtered.criticalCoreItems items))
      * Pair.weightedWorkSum rate work (Filtered.deepHighHighItems items)
  + Pair.natAsRational (length (Filtered.deepHighHighItems items))
      * Pair.weightedWorkSum rate work (Filtered.criticalCoreItems items)
  - Pair.rateSum rate (Filtered.deepHighHighItems items)
      * Pair.workSum work (Filtered.criticalCoreItems items)
  - Pair.rateSum rate (Filtered.criticalCoreItems items)
      * Pair.workSum work (Filtered.deepHighHighItems items)

defectCovarianceClosedForm :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  defectCovariance rate work items
  ≡ defectAggregateNormalForm rate work items
defectCovarianceClosedForm rate work items
  rewrite Filtered.deepFarLowCoreClosedForm rate work items
        | Filtered.deepHighHighCoreClosedForm rate work items = solve []

------------------------------------------------------------------------
-- Live same-object endpoint.
------------------------------------------------------------------------

module LiveDefectBipartite
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module R = SplitRows.LivePrincipalDefect physicalSystem S output

  liveDefectCovariance : ℚ
  liveDefectCovariance =
    defectCovariance Rate.inputMass (Live.work output) R.items

  liveDefectAggregate : ℚ
  liveDefectAggregate =
    defectAggregateNormalForm Rate.inputMass (Live.work output) R.items

  defectIsNegativeBipartite :
    R.defect ≡ 0ℚ - liveDefectCovariance
  defectIsNegativeBipartite =
    trans
      (SplitRows.defectRowsMeaning
        Rate.inputMass (Live.work output) R.items)
      (trans
        (splitDefectBlockIsNegativePositiveDefect
          (Blocks.pairBlocks Rate.inputMass (Live.work output) R.items))
        (cong (0ℚ -_)
          (positiveDefectPairBlocksMeaning
            Rate.inputMass (Live.work output) R.items)))

  defectIsNegativeFourAggregate :
    R.defect ≡ 0ℚ - liveDefectAggregate
  defectIsNegativeFourAggregate =
    trans
      defectIsNegativeBipartite
      (cong (0ℚ -_)
        (defectCovarianceClosedForm
          Rate.inputMass (Live.work output) R.items))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

b4DefectBipartiteSameObjectClosed : Bool
b4DefectBipartiteSameObjectClosed = true

b4DefectFourAggregateNormalFormClosed : Bool
b4DefectFourAggregateNormalFormClosed = true

b4DefectBipartiteEstimateClosed : Bool
b4DefectBipartiteEstimateClosed = false

b4DefectNormalFormIntroducesAbsoluteValue : Bool
b4DefectNormalFormIntroducesAbsoluteValue = false

clayPromotion : Bool
clayPromotion = false

b4DefectBipartiteSameObjectClosedIsTrue :
  b4DefectBipartiteSameObjectClosed ≡ true
b4DefectBipartiteSameObjectClosedIsTrue = refl

b4DefectFourAggregateNormalFormClosedIsTrue :
  b4DefectFourAggregateNormalFormClosed ≡ true
b4DefectFourAggregateNormalFormClosedIsTrue = refl

b4DefectBipartiteEstimateClosedIsFalse :
  b4DefectBipartiteEstimateClosed ≡ false
b4DefectBipartiteEstimateClosedIsFalse = refl
