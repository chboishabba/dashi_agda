module DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianThreeClassPairBlocksExact where

------------------------------------------------------------------------
-- S2b2d1b2 / 16 DIRECTIONAL BONY BLOCKS -> 6 UNORDERED THREE-CLASS BLOCKS
--
-- Merge LH and HL into the physical far-low class, but do it at the COMPLETE
-- pair-graph level where every summand still contains
--
--   (S_alpha-S_beta)(w_alpha-w_beta).
--
-- The resulting fixed six coordinates are
--
--   FL-FL, FL-HH, FL-CC, HH-HH, HH-CC, CC-CC.
--
-- This is exact scalar regrouping only.  No analytic observer is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianBonyPairBlocksExact as B16

record ThreeClassPairBlocks : Set where
  constructor three-class-pair-blocks
  field
    farLowFarLow
    farLowHighHigh
    farLowComparable
    highHighHighHigh
    highHighComparable
    comparableComparable : ℚ

open ThreeClassPairBlocks public

fromSixteen : B16.BonyPairBlocks → ThreeClassPairBlocks
fromSixteen blocks =
  three-class-pair-blocks
    ( (B16.lhToLH blocks + B16.hlToHL blocks)
      + (B16.lhToHL blocks + B16.hlToLH blocks) )

    ( (B16.lhToHH blocks + B16.hhToLH blocks)
      + (B16.hlToHH blocks + B16.hhToHL blocks) )

    ( (B16.lhToCC blocks + B16.ccToLH blocks)
      + (B16.hlToCC blocks + B16.ccToHL blocks) )

    (B16.hhToHH blocks)

    (B16.hhToCC blocks + B16.ccToHH blocks)

    (B16.ccToCC blocks)

sixBlockTotal : ThreeClassPairBlocks → ℚ
sixBlockTotal blocks =
    farLowFarLow blocks
  + farLowHighHigh blocks
  + farLowComparable blocks
  + highHighHighHigh blocks
  + highHighComparable blocks
  + comparableComparable blocks

sixBlockTotalIsSixteenBlockTotal :
  (blocks : B16.BonyPairBlocks) →
  sixBlockTotal (fromSixteen blocks)
  ≡ B16.blocksTotal blocks
sixBlockTotalIsSixteenBlockTotal blocks =
  solve
    ( B16.lhToLH blocks ∷ B16.lhToHL blocks
    ∷ B16.lhToHH blocks ∷ B16.lhToCC blocks
    ∷ B16.hlToLH blocks ∷ B16.hlToHL blocks
    ∷ B16.hlToHH blocks ∷ B16.hlToCC blocks
    ∷ B16.hhToLH blocks ∷ B16.hhToHL blocks
    ∷ B16.hhToHH blocks ∷ B16.hhToCC blocks
    ∷ B16.ccToLH blocks ∷ B16.ccToHL blocks
    ∷ B16.ccToHH blocks ∷ B16.ccToCC blocks
    ∷ [])

pairDifferenceIsSixThreeClassBlocks :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Pair.pairDifferenceWorkSum rate work items
  ≡ sixBlockTotal (fromSixteen (B16.pairBlocks rate work items))
pairDifferenceIsSixThreeClassBlocks rate work items =
  let
    sixteen =
      B16.pairDifferenceIsSixteenBonyBlocks rate work items
    regroup =
      sixBlockTotalIsSixteenBlockTotal (B16.pairBlocks rate work items)
  in
  trans sixteen (sym regroup)

completePairGraphThreeClassSixBlockLedgerClosed : Bool
completePairGraphThreeClassSixBlockLedgerClosed = true

farLowMergedOnlyAfterPairDifferenceFormed : Bool
farLowMergedOnlyAfterPairDifferenceFormed = true

threeClassPairLedgerIntroducesFibreCardinality : Bool
threeClassPairLedgerIntroducesFibreCardinality = false

threeClassPairLedgerIntroducesAbsoluteValue : Bool
threeClassPairLedgerIntroducesAbsoluteValue = false

clayPromotion : Bool
clayPromotion = false

completePairGraphThreeClassSixBlockLedgerClosedIsTrue :
  completePairGraphThreeClassSixBlockLedgerClosed ≡ true
completePairGraphThreeClassSixBlockLedgerClosedIsTrue = refl
