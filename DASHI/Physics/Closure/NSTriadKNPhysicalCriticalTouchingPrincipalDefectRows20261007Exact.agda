module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Exact where

------------------------------------------------------------------------
-- POSITIVE B4 / LITERAL PRINCIPAL-DEFECT ROW SPLIT / 2026-10-07
--
-- Work only on the SAME literal critical-touching unordered-pair carrier.
--
--   principal : Core-Core rows
--   defect    : Core-noncore rows (DFL-Core and DHH-Core, either orientation)
--
-- Besides the total split
--
--   criticalTouchingSigned = principal + defect,
--
-- this owner now identifies the two pieces individually with the already-live
-- R236 coordinates:
--
--   principal = coreCoreSigned,
--   defect    = deepFarLowCoreSigned + deepHighHighCoreSigned.
--
-- This is same-object algebra only.  No norm, estimate, shell count, alternate
-- observable, or synthetic carrier is introduced.  The two physical estimates
-- and their strict uniform margin remain open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; _++_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalParabolicCriticalRegionRoutingExact as Routing
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Rows
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralRowsMaxCutExact as Critical
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact as Blocks
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

------------------------------------------------------------------------
-- One-pair partition of the literal critical-touching selector.
------------------------------------------------------------------------

principalRoute :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
principalRoute alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion =
  Rows.literal-pair-row alpha beta ∷ []

defectRoute :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
defectRoute alpha beta
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
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = []

criticalRouteSumSplit :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (Critical.criticalTouchingRoute alpha beta)
  ≡ Rows.sumRows rate work (principalRoute alpha beta)
    + Rows.sumRows rate work (defectRoute alpha beta)
criticalRouteSumSplit rate work alpha beta
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

------------------------------------------------------------------------
-- Individual route meanings on the existing R236 block ledger.
------------------------------------------------------------------------

principalRouteMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (principalRoute alpha beta)
  ≡ 0ℚ - Blocks.criticalCoreCriticalCore
      (Blocks.routePair alpha beta (Blocks.pairTerm rate work alpha beta))
principalRouteMeaning rate work alpha beta
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

defectBlock : Blocks.RegionPairBlocks → ℚ
defectBlock blocks =
  (0ℚ - Blocks.deepFarLowCriticalCore blocks)
  + (0ℚ - Blocks.deepHighHighCriticalCore blocks)

defectRouteMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (defectRoute alpha beta)
  ≡ defectBlock
      (Blocks.routePair alpha beta (Blocks.pairTerm rate work alpha beta))
defectRouteMeaning rate work alpha beta
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

negativeCoreCoreAdd :
  (left right : Blocks.RegionPairBlocks) →
  0ℚ - Blocks.criticalCoreCriticalCore (Blocks.addBlocks left right)
  ≡ (0ℚ - Blocks.criticalCoreCriticalCore left)
    + (0ℚ - Blocks.criticalCoreCriticalCore right)
negativeCoreCoreAdd
  (Blocks.region-pair-blocks
    (Blocks.region-row a b c) (Blocks.region-row d e f) (Blocks.region-row g h i))
  (Blocks.region-pair-blocks
    (Blocks.region-row j k l) (Blocks.region-row m n o) (Blocks.region-row p q r)) =
  solve (i ∷ r ∷ [])

defectBlockAdd :
  (left right : Blocks.RegionPairBlocks) →
  defectBlock (Blocks.addBlocks left right)
  ≡ defectBlock left + defectBlock right
defectBlockAdd
  (Blocks.region-pair-blocks
    (Blocks.region-row a b c) (Blocks.region-row d e f) (Blocks.region-row g h i))
  (Blocks.region-pair-blocks
    (Blocks.region-row j k l) (Blocks.region-row m n o) (Blocks.region-row p q r)) =
  solve (c ∷ f ∷ g ∷ h ∷ l ∷ o ∷ p ∷ q ∷ [])

------------------------------------------------------------------------
-- Replay the same unordered-pair recursion for principal and defect rows.
------------------------------------------------------------------------

principalAgainst :
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
principalAgainst head [] = []
principalAgainst head (x ∷ xs) =
  principalRoute head x ++ principalAgainst head xs

defectAgainst :
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
defectAgainst head [] = []
defectAgainst head (x ∷ xs) =
  defectRoute head x ++ defectAgainst head xs

principalRows : List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
principalRows [] = []
principalRows (head ∷ rest) = principalAgainst head rest ++ principalRows rest

defectRows : List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
defectRows [] = []
defectRows (head ∷ rest) = defectAgainst head rest ++ defectRows rest

criticalAgainstSumSplit :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (Critical.criticalTouchingAgainst head rest)
  ≡ Rows.sumRows rate work (principalAgainst head rest)
    + Rows.sumRows rate work (defectAgainst head rest)
criticalAgainstSumSplit rate work head [] = solve []
criticalAgainstSumSplit rate work head (x ∷ xs)
  rewrite Rows.sumRowsAppend rate work
            (Critical.criticalTouchingRoute head x)
            (Critical.criticalTouchingAgainst head xs)
        | Rows.sumRowsAppend rate work
            (principalRoute head x)
            (principalAgainst head xs)
        | Rows.sumRowsAppend rate work
            (defectRoute head x)
            (defectAgainst head xs)
        | criticalRouteSumSplit rate work head x
        | criticalAgainstSumSplit rate work head xs = solve []

principalAgainstMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (principalAgainst head rest)
  ≡ 0ℚ - Blocks.criticalCoreCriticalCore
      (Blocks.blocksAgainstHead rate work head rest)
principalAgainstMeaning rate work head [] = solve []
principalAgainstMeaning rate work head (x ∷ xs) =
  trans
    (Rows.sumRowsAppend rate work
      (principalRoute head x)
      (principalAgainst head xs))
    (trans
      (cong₂ _+_
        (principalRouteMeaning rate work head x)
        (principalAgainstMeaning rate work head xs))
      (sym
        (negativeCoreCoreAdd
          (Blocks.routePair head x (Blocks.pairTerm rate work head x))
          (Blocks.blocksAgainstHead rate work head xs))))

defectAgainstMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (defectAgainst head rest)
  ≡ defectBlock (Blocks.blocksAgainstHead rate work head rest)
defectAgainstMeaning rate work head [] = solve []
defectAgainstMeaning rate work head (x ∷ xs) =
  trans
    (Rows.sumRowsAppend rate work
      (defectRoute head x)
      (defectAgainst head xs))
    (trans
      (cong₂ _+_
        (defectRouteMeaning rate work head x)
        (defectAgainstMeaning rate work head xs))
      (sym
        (defectBlockAdd
          (Blocks.routePair head x (Blocks.pairTerm rate work head x))
          (Blocks.blocksAgainstHead rate work head xs))))

criticalRowsSumSplit :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (Critical.criticalTouchingRows items)
  ≡ Rows.sumRows rate work (principalRows items)
    + Rows.sumRows rate work (defectRows items)
criticalRowsSumSplit rate work [] = solve []
criticalRowsSumSplit rate work (head ∷ rest)
  rewrite Rows.sumRowsAppend rate work
            (Critical.criticalTouchingAgainst head rest)
            (Critical.criticalTouchingRows rest)
        | Rows.sumRowsAppend rate work
            (principalAgainst head rest)
            (principalRows rest)
        | Rows.sumRowsAppend rate work
            (defectAgainst head rest)
            (defectRows rest)
        | criticalAgainstSumSplit rate work head rest
        | criticalRowsSumSplit rate work rest = solve []

principalRowsMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (principalRows items)
  ≡ 0ℚ - Blocks.criticalCoreCriticalCore (Blocks.pairBlocks rate work items)
principalRowsMeaning rate work [] = solve []
principalRowsMeaning rate work (head ∷ rest) =
  trans
    (Rows.sumRowsAppend rate work
      (principalAgainst head rest)
      (principalRows rest))
    (trans
      (cong₂ _+_
        (principalAgainstMeaning rate work head rest)
        (principalRowsMeaning rate work rest))
      (sym
        (negativeCoreCoreAdd
          (Blocks.blocksAgainstHead rate work head rest)
          (Blocks.pairBlocks rate work rest))))

defectRowsMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (defectRows items)
  ≡ defectBlock (Blocks.pairBlocks rate work items)
defectRowsMeaning rate work [] = solve []
defectRowsMeaning rate work (head ∷ rest) =
  trans
    (Rows.sumRowsAppend rate work
      (defectAgainst head rest)
      (defectRows rest))
    (trans
      (cong₂ _+_
        (defectAgainstMeaning rate work head rest)
        (defectRowsMeaning rate work rest))
      (sym
        (defectBlockAdd
          (Blocks.blocksAgainstHead rate work head rest)
          (Blocks.pairBlocks rate work rest))))

------------------------------------------------------------------------
-- Live physical same-object split and individual R236 coordinate welds.
------------------------------------------------------------------------

module LivePrincipalDefect
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module Exact = RegionLive.LiveRegion physicalSystem S output
  module C = Critical.LiveCriticalRows physicalSystem S output
  module P = Pay.LiveRegionPayment physicalSystem S output

  items : List Physical.PhysicalTriadIncidence
  items = Live.fibre output

  principalLiteralRows : List Rows.LiteralPairRow
  principalLiteralRows = principalRows items

  defectLiteralRows : List Rows.LiteralPairRow
  defectLiteralRows = defectRows items

  principal : ℚ
  principal = Rows.sumRows Rate.inputMass (Live.work output) principalLiteralRows

  defect : ℚ
  defect = Rows.sumRows Rate.inputMass (Live.work output) defectLiteralRows

  literalRowSumSplit : C.rowSum ≡ principal + defect
  literalRowSumSplit =
    criticalRowsSumSplit Rate.inputMass (Live.work output) items

  principalIsLiveCoreCore : principal ≡ P.coreCoreSigned
  principalIsLiveCoreCore =
    principalRowsMeaning Rate.inputMass (Live.work output) items

  defectIsLiveCoreNoncore :
    defect ≡ P.deepFarLowCoreSigned + P.deepHighHighCoreSigned
  defectIsLiveCoreNoncore =
    defectRowsMeaning Rate.inputMass (Live.work output) items

  liveCriticalTouchingSplit : P.criticalTouchingSigned ≡ principal + defect
  liveCriticalTouchingSplit =
    trans C.liveCriticalTouchingIsLiteralRows literalRowSumSplit

------------------------------------------------------------------------
-- Status: decomposition and live-block weld are closed; estimates are not.
------------------------------------------------------------------------

b4LiteralPrincipalDefectSplitClosed : Bool
b4LiteralPrincipalDefectSplitClosed = true

b4PrincipalDefectLiveBlockWeldClosed : Bool
b4PrincipalDefectLiveBlockWeldClosed = true

b4PrincipalIsLiteralCoreCoreRows : Bool
b4PrincipalIsLiteralCoreCoreRows = true

b4DefectIsLiteralCoreNoncoreRows : Bool
b4DefectIsLiteralCoreNoncoreRows = true

b4PrincipalPhysicalEstimateClosedHere : Bool
b4PrincipalPhysicalEstimateClosedHere = false

b4DefectPhysicalEstimateClosedHere : Bool
b4DefectPhysicalEstimateClosedHere = false

b4SplitIntroducesEstimate : Bool
b4SplitIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

b4LiteralPrincipalDefectSplitClosedIsTrue :
  b4LiteralPrincipalDefectSplitClosed ≡ true
b4LiteralPrincipalDefectSplitClosedIsTrue = refl

b4PrincipalDefectLiveBlockWeldClosedIsTrue :
  b4PrincipalDefectLiveBlockWeldClosed ≡ true
b4PrincipalDefectLiveBlockWeldClosedIsTrue = refl

b4PrincipalPhysicalEstimateClosedHereIsFalse :
  b4PrincipalPhysicalEstimateClosedHere ≡ false
b4PrincipalPhysicalEstimateClosedHereIsFalse = refl

b4DefectPhysicalEstimateClosedHereIsFalse :
  b4DefectPhysicalEstimateClosedHere ≡ false
b4DefectPhysicalEstimateClosedHereIsFalse = refl
