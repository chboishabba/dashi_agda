module DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianBonyPairBlocksExact where

------------------------------------------------------------------------
-- S2b2d1b2 / COMPLETE PAIR GRAPH -> FIXED 4 x 4 BONY BLOCK LEDGER
--
-- Splitting the globally-centered vector is algebraically exact, but estimating
-- its class pieces separately can expose the global coefficient
--
--   n S_tau - S_tot
--
-- and thereby risk reintroducing fibre-cardinality loss.
--
-- The quantitatively safer object is the COMPLETE pair graph itself:
--
--   sum_{alpha<beta} (S_alpha-S_beta)(w_alpha-w_beta).
--
-- Route each pair by the physical Bony tags of alpha and beta.  This owner
-- constructs a fixed 4 x 4 ledger (LH, HL, HH->low, comparable on each side)
-- and proves exactly
--
--   pairDifferenceWorkSum = total of the 16 routed blocks.
--
-- Every block retains the multiplier DIFFERENCE.  No n, class average,
-- absolute value, norm, Cauchy/Young/Schur step, shell count, or cutoff factor
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair

------------------------------------------------------------------------
-- One row: class of beta for a fixed class of alpha.
------------------------------------------------------------------------

record BonyRow : Set where
  constructor bony-row
  field
    toLH toHL toHH toCC : ℚ

open BonyRow public

zeroRow : BonyRow
zeroRow = bony-row 0ℚ 0ℚ 0ℚ 0ℚ

addRow : BonyRow → BonyRow → BonyRow
addRow left right =
  bony-row
    (toLH left + toLH right)
    (toHL left + toHL right)
    (toHH left + toHH right)
    (toCC left + toCC right)

rowTotal : BonyRow → ℚ
rowTotal row =
  (toLH row + toHL row) + (toHH row + toCC row)

addRowTotal :
  (left right : BonyRow) →
  rowTotal (addRow left right)
  ≡ rowTotal left + rowTotal right
addRowTotal
    (bony-row a b c d)
    (bony-row e f g h) =
  solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])

routeRight : Physical.PhysicalTriadIncidence → ℚ → BonyRow
routeRight tau value with Bony.bonyTag tau
... | Bony.lhTag = bony-row value 0ℚ 0ℚ 0ℚ
... | Bony.hlTag = bony-row 0ℚ value 0ℚ 0ℚ
... | Bony.hhToLowTag = bony-row 0ℚ 0ℚ value 0ℚ
... | Bony.comparableTag = bony-row 0ℚ 0ℚ 0ℚ value

routeRightTotal :
  (tau : Physical.PhysicalTriadIncidence) →
  (value : ℚ) →
  rowTotal (routeRight tau value) ≡ value
routeRightTotal tau value with Bony.bonyTag tau
... | Bony.lhTag = solve (value ∷ [])
... | Bony.hlTag = solve (value ∷ [])
... | Bony.hhToLowTag = solve (value ∷ [])
... | Bony.comparableTag = solve (value ∷ [])

------------------------------------------------------------------------
-- Four rows: class of alpha.
------------------------------------------------------------------------

record BonyPairBlocks : Set where
  constructor bony-pair-blocks
  field
    fromLH fromHL fromHH fromCC : BonyRow

open BonyPairBlocks public

zeroBlocks : BonyPairBlocks
zeroBlocks =
  bony-pair-blocks zeroRow zeroRow zeroRow zeroRow

addBlocks : BonyPairBlocks → BonyPairBlocks → BonyPairBlocks
addBlocks left right =
  bony-pair-blocks
    (addRow (fromLH left) (fromLH right))
    (addRow (fromHL left) (fromHL right))
    (addRow (fromHH left) (fromHH right))
    (addRow (fromCC left) (fromCC right))

blocksTotal : BonyPairBlocks → ℚ
blocksTotal blocks =
  (rowTotal (fromLH blocks) + rowTotal (fromHL blocks))
  + (rowTotal (fromHH blocks) + rowTotal (fromCC blocks))

addBlocksTotal :
  (left right : BonyPairBlocks) →
  blocksTotal (addBlocks left right)
  ≡ blocksTotal left + blocksTotal right
addBlocksTotal left right
  rewrite addRowTotal (fromLH left) (fromLH right)
        | addRowTotal (fromHL left) (fromHL right)
        | addRowTotal (fromHH left) (fromHH right)
        | addRowTotal (fromCC left) (fromCC right) =
  solve
    ( rowTotal (fromLH left) ∷ rowTotal (fromHL left)
    ∷ rowTotal (fromHH left) ∷ rowTotal (fromCC left)
    ∷ rowTotal (fromLH right) ∷ rowTotal (fromHL right)
    ∷ rowTotal (fromHH right) ∷ rowTotal (fromCC right)
    ∷ [])

routePair :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence →
  ℚ → BonyPairBlocks
routePair alpha beta value with Bony.bonyTag alpha
... | Bony.lhTag =
  bony-pair-blocks (routeRight beta value) zeroRow zeroRow zeroRow
... | Bony.hlTag =
  bony-pair-blocks zeroRow (routeRight beta value) zeroRow zeroRow
... | Bony.hhToLowTag =
  bony-pair-blocks zeroRow zeroRow (routeRight beta value) zeroRow
... | Bony.comparableTag =
  bony-pair-blocks zeroRow zeroRow zeroRow (routeRight beta value)

routePairTotal :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  (value : ℚ) →
  blocksTotal (routePair alpha beta value) ≡ value
routePairTotal alpha beta value with Bony.bonyTag alpha
... | Bony.lhTag
  rewrite routeRightTotal beta value =
  solve (value ∷ [])
... | Bony.hlTag
  rewrite routeRightTotal beta value =
  solve (value ∷ [])
... | Bony.hhToLowTag
  rewrite routeRightTotal beta value =
  solve (value ∷ [])
... | Bony.comparableTag
  rewrite routeRightTotal beta value =
  solve (value ∷ [])

------------------------------------------------------------------------
-- Route the exact complete-graph pair term.
------------------------------------------------------------------------

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
  BonyPairBlocks
blocksAgainstHead rate work head [] = zeroBlocks
blocksAgainstHead rate work head (x ∷ xs) =
  addBlocks
    (routePair head x (pairTerm rate work head x))
    (blocksAgainstHead rate work head xs)

pairBlocks :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence →
  BonyPairBlocks
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
    (trans
      (cong₂ _+_
        (routePairTotal head x (pairTerm rate work head x))
        (blocksAgainstHeadMeaning rate work head xs))
      refl)

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

pairDifferenceIsSixteenBonyBlocks :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Pair.pairDifferenceWorkSum rate work items
  ≡ blocksTotal (pairBlocks rate work items)
pairDifferenceIsSixteenBonyBlocks rate work items =
  sym (pairBlocksMeaning rate work items)

------------------------------------------------------------------------
-- Useful named block accessors.
------------------------------------------------------------------------

lhToLH lhToHL lhToHH lhToCC
  hlToLH hlToHL hlToHH hlToCC
  hhToLH hhToHL hhToHH hhToCC
  ccToLH ccToHL ccToHH ccToCC :
  BonyPairBlocks → ℚ

lhToLH blocks = toLH (fromLH blocks)
lhToHL blocks = toHL (fromLH blocks)
lhToHH blocks = toHH (fromLH blocks)
lhToCC blocks = toCC (fromLH blocks)

hlToLH blocks = toLH (fromHL blocks)
hlToHL blocks = toHL (fromHL blocks)
hlToHH blocks = toHH (fromHL blocks)
hlToCC blocks = toCC (fromHL blocks)

hhToLH blocks = toLH (fromHH blocks)
hhToHL blocks = toHL (fromHH blocks)
hhToHH blocks = toHH (fromHH blocks)
hhToCC blocks = toCC (fromHH blocks)

ccToLH blocks = toLH (fromCC blocks)
ccToHL blocks = toHL (fromCC blocks)
ccToHH blocks = toHH (fromCC blocks)
ccToCC blocks = toCC (fromCC blocks)

completePairGraphBonyBlockLedgerClosed : Bool
completePairGraphBonyBlockLedgerClosed = true

pairBlockLedgerRetainsMultiplierDifferences : Bool
pairBlockLedgerRetainsMultiplierDifferences = true

pairBlockLedgerIntroducesFibreCardinality : Bool
pairBlockLedgerIntroducesFibreCardinality = false

pairBlockLedgerIntroducesAbsoluteValue : Bool
pairBlockLedgerIntroducesAbsoluteValue = false

pairBlockLedgerIntroducesNorm : Bool
pairBlockLedgerIntroducesNorm = false

clayPromotion : Bool
clayPromotion = false

completePairGraphBonyBlockLedgerClosedIsTrue :
  completePairGraphBonyBlockLedgerClosed ≡ true
completePairGraphBonyBlockLedgerClosedIsTrue = refl
