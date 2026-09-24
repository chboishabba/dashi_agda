module DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact where

------------------------------------------------------------------------
-- S2b2d1b2 / COMPLETE PAIR GRAPH -> 3 x 3 PHYSICAL R236 REGION LEDGER
--
-- Route each literal pair only AFTER the good multiplier-difference form
--
--   (S_alpha-S_beta)(w_alpha-w_beta)
--
-- has been formed.  The per-incidence classifier is the actual physical
-- R236 deep-FL / deep-HH / critical-core routing.
--
-- The directional 3 x 3 ledger is then compressed to the six unordered blocks
--
--   DFL-DFL, DFL-DHH, DFL-Core, DHH-DHH, DHH-Core, Core-Core.
--
-- No global n*S-S_tot coefficient is exposed and no analytic observer enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNPhysicalParabolicCriticalRegionRoutingExact as Region

record RegionRow : Set where
  constructor region-row
  field
    toDeepFarLow toDeepHighHigh toCriticalCore : ℚ

open RegionRow public

zeroRow : RegionRow
zeroRow = region-row 0ℚ 0ℚ 0ℚ

addRow : RegionRow → RegionRow → RegionRow
addRow left right =
  region-row
    (toDeepFarLow left + toDeepFarLow right)
    (toDeepHighHigh left + toDeepHighHigh right)
    (toCriticalCore left + toCriticalCore right)

rowTotal : RegionRow → ℚ
rowTotal row =
  toDeepFarLow row + toDeepHighHigh row + toCriticalCore row

addRowTotal :
  (left right : RegionRow) →
  rowTotal (addRow left right)
  ≡ rowTotal left + rowTotal right
addRowTotal
    (region-row a b c)
    (region-row d e f) =
  solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

routeRight :
  Physical.PhysicalTriadIncidence → ℚ → RegionRow
routeRight tau value with Region.criticalRegionTag tau
... | Region.deepFarLowRegion = region-row value 0ℚ 0ℚ
... | Region.deepHighHighRegion = region-row 0ℚ value 0ℚ
... | Region.criticalCoreRegion = region-row 0ℚ 0ℚ value

routeRightTotal :
  (tau : Physical.PhysicalTriadIncidence) →
  (value : ℚ) →
  rowTotal (routeRight tau value) ≡ value
routeRightTotal tau value with Region.criticalRegionTag tau
... | Region.deepFarLowRegion = solve (value ∷ [])
... | Region.deepHighHighRegion = solve (value ∷ [])
... | Region.criticalCoreRegion = solve (value ∷ [])

record RegionPairBlocks : Set where
  constructor region-pair-blocks
  field
    fromDeepFarLow fromDeepHighHigh fromCriticalCore : RegionRow

open RegionPairBlocks public

zeroBlocks : RegionPairBlocks
zeroBlocks =
  region-pair-blocks zeroRow zeroRow zeroRow

addBlocks : RegionPairBlocks → RegionPairBlocks → RegionPairBlocks
addBlocks left right =
  region-pair-blocks
    (addRow (fromDeepFarLow left) (fromDeepFarLow right))
    (addRow (fromDeepHighHigh left) (fromDeepHighHigh right))
    (addRow (fromCriticalCore left) (fromCriticalCore right))

blocksTotal : RegionPairBlocks → ℚ
blocksTotal blocks =
    rowTotal (fromDeepFarLow blocks)
  + rowTotal (fromDeepHighHigh blocks)
  + rowTotal (fromCriticalCore blocks)

addBlocksTotal :
  (left right : RegionPairBlocks) →
  blocksTotal (addBlocks left right)
  ≡ blocksTotal left + blocksTotal right
addBlocksTotal left right
  rewrite addRowTotal (fromDeepFarLow left) (fromDeepFarLow right)
        | addRowTotal (fromDeepHighHigh left) (fromDeepHighHigh right)
        | addRowTotal (fromCriticalCore left) (fromCriticalCore right) =
  solve
    ( rowTotal (fromDeepFarLow left)
    ∷ rowTotal (fromDeepHighHigh left)
    ∷ rowTotal (fromCriticalCore left)
    ∷ rowTotal (fromDeepFarLow right)
    ∷ rowTotal (fromDeepHighHigh right)
    ∷ rowTotal (fromCriticalCore right)
    ∷ [])

routePair :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence →
  ℚ → RegionPairBlocks
routePair alpha beta value with Region.criticalRegionTag alpha
... | Region.deepFarLowRegion =
  region-pair-blocks (routeRight beta value) zeroRow zeroRow
... | Region.deepHighHighRegion =
  region-pair-blocks zeroRow (routeRight beta value) zeroRow
... | Region.criticalCoreRegion =
  region-pair-blocks zeroRow zeroRow (routeRight beta value)

routePairTotal :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  (value : ℚ) →
  blocksTotal (routePair alpha beta value) ≡ value
routePairTotal alpha beta value with Region.criticalRegionTag alpha
... | Region.deepFarLowRegion
  rewrite routeRightTotal beta value =
  solve (value ∷ [])
... | Region.deepHighHighRegion
  rewrite routeRightTotal beta value =
  solve (value ∷ [])
... | Region.criticalCoreRegion
  rewrite routeRightTotal beta value =
  solve (value ∷ [])

pairTerm :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
pairTerm rate work alpha beta =
  (rate alpha - rate beta) * (work alpha - work beta)

blocksAgainstHead :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence →
  RegionPairBlocks
blocksAgainstHead rate work head [] = zeroBlocks
blocksAgainstHead rate work head (x ∷ xs) =
  addBlocks
    (routePair head x (pairTerm rate work head x))
    (blocksAgainstHead rate work head xs)

pairBlocks :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence →
  RegionPairBlocks
pairBlocks rate work [] = zeroBlocks
pairBlocks rate work (head ∷ rest) =
  addBlocks
    (blocksAgainstHead rate work head rest)
    (pairBlocks rate work rest)

blocksAgainstHeadMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  blocksTotal (blocksAgainstHead rate work head rest)
  ≡ Pair.pairAgainstHead rate work head rest
blocksAgainstHeadMeaning rate work head [] = refl
blocksAgainstHeadMeaning rate work head (x ∷ xs) =
  trans
    (addBlocksTotal
      (routePair head x (pairTerm rate work head x))
      (blocksAgainstHead rate work head xs))
    (cong₂ _+_
      (routePairTotal head x (pairTerm rate work head x))
      (blocksAgainstHeadMeaning rate work head xs))

pairBlocksMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  blocksTotal (pairBlocks rate work items)
  ≡ Pair.pairDifferenceWorkSum rate work items
pairBlocksMeaning rate work [] = refl
pairBlocksMeaning rate work (head ∷ rest) =
  trans
    (addBlocksTotal
      (blocksAgainstHead rate work head rest)
      (pairBlocks rate work rest))
    (cong₂ _+_
      (blocksAgainstHeadMeaning rate work head rest)
      (pairBlocksMeaning rate work rest))

------------------------------------------------------------------------
-- Six unordered physical-region coordinates.
------------------------------------------------------------------------

deepFarLowDeepFarLow
deepFarLowDeepHighHigh
deepFarLowCriticalCore
deepHighHighDeepHighHigh
deepHighHighCriticalCore
criticalCoreCriticalCore :
  RegionPairBlocks → ℚ

deepFarLowDeepFarLow blocks =
  toDeepFarLow (fromDeepFarLow blocks)

deepFarLowDeepHighHigh blocks =
  toDeepHighHigh (fromDeepFarLow blocks)
  + toDeepFarLow (fromDeepHighHigh blocks)

deepFarLowCriticalCore blocks =
  toCriticalCore (fromDeepFarLow blocks)
  + toDeepFarLow (fromCriticalCore blocks)

deepHighHighDeepHighHigh blocks =
  toDeepHighHigh (fromDeepHighHigh blocks)

deepHighHighCriticalCore blocks =
  toCriticalCore (fromDeepHighHigh blocks)
  + toDeepHighHigh (fromCriticalCore blocks)

criticalCoreCriticalCore blocks =
  toCriticalCore (fromCriticalCore blocks)

sixRegionTotal : RegionPairBlocks → ℚ
sixRegionTotal blocks =
    deepFarLowDeepFarLow blocks
  + deepFarLowDeepHighHigh blocks
  + deepFarLowCriticalCore blocks
  + deepHighHighDeepHighHigh blocks
  + deepHighHighCriticalCore blocks
  + criticalCoreCriticalCore blocks

sixRegionTotalIsBlocksTotal :
  (blocks : RegionPairBlocks) →
  sixRegionTotal blocks ≡ blocksTotal blocks
sixRegionTotalIsBlocksTotal blocks =
  solve
    ( toDeepFarLow (fromDeepFarLow blocks)
    ∷ toDeepHighHigh (fromDeepFarLow blocks)
    ∷ toCriticalCore (fromDeepFarLow blocks)
    ∷ toDeepFarLow (fromDeepHighHigh blocks)
    ∷ toDeepHighHigh (fromDeepHighHigh blocks)
    ∷ toCriticalCore (fromDeepHighHigh blocks)
    ∷ toDeepFarLow (fromCriticalCore blocks)
    ∷ toDeepHighHigh (fromCriticalCore blocks)
    ∷ toCriticalCore (fromCriticalCore blocks)
    ∷ [])

pairDifferenceIsSixPhysicalRegionBlocks :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Pair.pairDifferenceWorkSum rate work items
  ≡ sixRegionTotal (pairBlocks rate work items)
pairDifferenceIsSixPhysicalRegionBlocks rate work items =
  trans
    (sym (pairBlocksMeaning rate work items))
    (sym (sixRegionTotalIsBlocksTotal (pairBlocks rate work items)))

literalCriticalRegionPairLedgerClosed : Bool
literalCriticalRegionPairLedgerClosed = true

literalCriticalRegionPairLedgerRetainsMultiplierDifferences : Bool
literalCriticalRegionPairLedgerRetainsMultiplierDifferences = true

literalCriticalRegionPairLedgerIntroducesFibreCardinality : Bool
literalCriticalRegionPairLedgerIntroducesFibreCardinality = false

literalCriticalRegionPairLedgerIntroducesNorm : Bool
literalCriticalRegionPairLedgerIntroducesNorm = false

clayPromotion : Bool
clayPromotion = false

literalCriticalRegionPairLedgerClosedIsTrue :
  literalCriticalRegionPairLedgerClosed ≡ true
literalCriticalRegionPairLedgerClosedIsTrue = refl
