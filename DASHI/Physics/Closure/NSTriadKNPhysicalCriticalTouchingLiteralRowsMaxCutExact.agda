module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralRowsMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B4 / EXACT LITERAL CRITICAL-TOUCHING PAIR ROWS
--
-- The scalar criticalTouchingSigned is the sum of the three R236 blocks
--
--   DFL-Core + DHH-Core + Core-Core
--
-- with the live sign convention.  For analytic work it is more useful to keep
-- the original unordered physical pair rows.  This owner replays the SAME
-- complete-pair recursion and selects exactly those rows for which at least one
-- incidence is tagged criticalCoreRegion.
--
-- No estimate, absolute value, norm, shell count or alternate observable is
-- introduced.  The terminal theorem identifies the literal row fold with the
-- SAME live `criticalTouchingSigned` scalar consumed by B4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; _++_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalParabolicCriticalRegionRoutingExact as Routing
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact as Blocks
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Rows
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceCriticalRegionLiveExact as RegionLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay

F : C3.RealField _
F = Rational.rationalRealField

criticalTouchingBlock : Blocks.RegionPairBlocks → ℚ
criticalTouchingBlock blocks =
    Blocks.deepFarLowCriticalCore blocks
  + Blocks.deepHighHighCriticalCore blocks
  + Blocks.criticalCoreCriticalCore blocks

criticalTouchingRoute :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
criticalTouchingRoute alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion =
  Rows.literal-pair-row alpha beta ∷ []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion =
  Rows.literal-pair-row alpha beta ∷ []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion =
  Rows.literal-pair-row alpha beta ∷ []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion =
  Rows.literal-pair-row alpha beta ∷ []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion =
  Rows.literal-pair-row alpha beta ∷ []

criticalTouchingRouteMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (criticalTouchingRoute alpha beta)
  ≡ 0ℚ - criticalTouchingBlock
      (Blocks.routePair alpha beta (Blocks.pairTerm rate work alpha beta))
criticalTouchingRouteMeaning rate work alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = refl
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = refl
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = solve []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = refl
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = refl
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = solve []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = solve []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = solve []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = solve []

negativeCriticalTouchingAdd :
  (left right : Blocks.RegionPairBlocks) →
  0ℚ - criticalTouchingBlock (Blocks.addBlocks left right)
  ≡ (0ℚ - criticalTouchingBlock left)
    + (0ℚ - criticalTouchingBlock right)
negativeCriticalTouchingAdd
  (Blocks.region-pair-blocks
    (Blocks.region-row a b c) (Blocks.region-row d e f) (Blocks.region-row g h i))
  (Blocks.region-pair-blocks
    (Blocks.region-row j k l) (Blocks.region-row m n o) (Blocks.region-row p q r)) =
  solve (c ∷ f ∷ g ∷ h ∷ i ∷ l ∷ o ∷ p ∷ q ∷ r ∷ [])

criticalTouchingAgainst :
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
criticalTouchingAgainst head [] = []
criticalTouchingAgainst head (x ∷ xs) =
  criticalTouchingRoute head x ++ criticalTouchingAgainst head xs

criticalTouchingRows :
  List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
criticalTouchingRows [] = []
criticalTouchingRows (head ∷ rest) =
  criticalTouchingAgainst head rest ++ criticalTouchingRows rest

criticalTouchingAgainstMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (criticalTouchingAgainst head rest)
  ≡ 0ℚ - criticalTouchingBlock
      (Blocks.blocksAgainstHead rate work head rest)
criticalTouchingAgainstMeaning rate work head [] = refl
criticalTouchingAgainstMeaning rate work head (x ∷ xs) =
  trans
    (Rows.sumRowsAppend rate work
      (criticalTouchingRoute head x)
      (criticalTouchingAgainst head xs))
    (trans
      (cong₂ _+_
        (criticalTouchingRouteMeaning rate work head x)
        (criticalTouchingAgainstMeaning rate work head xs))
      (sym
        (negativeCriticalTouchingAdd
          (Blocks.routePair head x (Blocks.pairTerm rate work head x))
          (Blocks.blocksAgainstHead rate work head xs))))

criticalTouchingRowsMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (criticalTouchingRows items)
  ≡ 0ℚ - criticalTouchingBlock (Blocks.pairBlocks rate work items)
criticalTouchingRowsMeaning rate work [] = refl
criticalTouchingRowsMeaning rate work (head ∷ rest) =
  trans
    (Rows.sumRowsAppend rate work
      (criticalTouchingAgainst head rest)
      (criticalTouchingRows rest))
    (trans
      (cong₂ _+_
        (criticalTouchingAgainstMeaning rate work head rest)
        (criticalTouchingRowsMeaning rate work rest))
      (sym
        (negativeCriticalTouchingAdd
          (Blocks.blocksAgainstHead rate work head rest)
          (Blocks.pairBlocks rate work rest))))

module LiveCriticalRows
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module Exact = RegionLive.LiveRegion physicalSystem S output
  module P = Pay.LiveRegionPayment physicalSystem S output

  items : List Physical.PhysicalTriadIncidence
  items = Live.fibre output

  rows : List Rows.LiteralPairRow
  rows = criticalTouchingRows items

  rowSum : ℚ
  rowSum = Rows.sumRows Rate.inputMass (Live.work output) rows

  rowSumIsNegativeCriticalTouchingBlock :
    rowSum ≡ 0ℚ - criticalTouchingBlock Exact.regionBlocks
  rowSumIsNegativeCriticalTouchingBlock =
    criticalTouchingRowsMeaning
      Rate.inputMass (Live.work output) items

  negativeBlockIsLiveCriticalTouching :
    0ℚ - criticalTouchingBlock Exact.regionBlocks
    ≡ P.criticalTouchingSigned
  negativeBlockIsLiveCriticalTouching =
    solve
      ( Blocks.deepFarLowCriticalCore Exact.regionBlocks
      ∷ Blocks.deepHighHighCriticalCore Exact.regionBlocks
      ∷ Blocks.criticalCoreCriticalCore Exact.regionBlocks
      ∷ [])

  liveCriticalTouchingIsLiteralRows :
    P.criticalTouchingSigned ≡ rowSum
  liveCriticalTouchingIsLiteralRows =
    sym
      (trans
        rowSumIsNegativeCriticalTouchingBlock
        negativeBlockIsLiveCriticalTouching)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

b4CriticalTouchingLiteralRowsExtracted : Bool
b4CriticalTouchingLiteralRowsExtracted = true

b4CriticalTouchingRowsSameObjectClosed : Bool
b4CriticalTouchingRowsSameObjectClosed = true

b4CriticalTouchingRowsRetainSignedMultiplierDifference : Bool
b4CriticalTouchingRowsRetainSignedMultiplierDifference = true

b4CriticalTouchingRowsIntroduceNorm : Bool
b4CriticalTouchingRowsIntroduceNorm = false

b4StrictThetaEstimateClosedHere : Bool
b4StrictThetaEstimateClosedHere = false

clayPromotion : Bool
clayPromotion = false

b4CriticalTouchingLiteralRowsExtractedIsTrue :
  b4CriticalTouchingLiteralRowsExtracted ≡ true
b4CriticalTouchingLiteralRowsExtractedIsTrue = refl

b4CriticalTouchingRowsSameObjectClosedIsTrue :
  b4CriticalTouchingRowsSameObjectClosed ≡ true
b4CriticalTouchingRowsSameObjectClosedIsTrue = refl

b4StrictThetaEstimateClosedHereIsFalse :
  b4StrictThetaEstimateClosedHere ≡ false
b4StrictThetaEstimateClosedHereIsFalse = refl
