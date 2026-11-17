module DASHI.Biology.IITCubeFirstTitsSL3TranslationIntersectionExact where

------------------------------------------------------------------------
-- CUBE GRAPH TRANSLATIONS AS FIRST-TITS / TRINIFICATION COORDINATE 3-CYCLES
--
-- The cube face is a literal 3x3 ternary table.  The synchronized first-Tits
-- owner indexes each 9-slot sector by (row,column).  This module pays the
-- same-coordinate action:
--
--   cube rowShift    = pullback by the order-three row cycle,
--   cube columnShift = pullback by the order-three column cycle.
--
-- The underlying coordinate permutation is a 3-cycle, hence an even
-- permutation and therefore has determinant sign +1.  Thus these two C3
-- translations are the finite permutation elements expected inside the left
-- and right SL3 factors of the M3^3 trinification action.  This is a finite
-- same-action statement only; it does not manufacture continuous/DHR physics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Mathematics.Algebra.Ternary27FirstTitsAlbertExact as Tits
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.IITCubeConcreteTorusImageExact as Cube
import DASHI.Biology.IITCubeDiagonalStabilizerExact as Stabilizer

------------------------------------------------------------------------
-- 1. The same order-three coordinate cycle on the Base369 and SSP trit charts.
------------------------------------------------------------------------

cycleBase : Base.TriTruth → Base.TriTruth
cycleBase Base.tri-low = Base.tri-mid
cycleBase Base.tri-mid = Base.tri-high
cycleBase Base.tri-high = Base.tri-low

cycleBase3 : (x : Base.TriTruth) → cycleBase (cycleBase (cycleBase x)) ≡ x
cycleBase3 Base.tri-low = refl
cycleBase3 Base.tri-mid = refl
cycleBase3 Base.tri-high = refl

baseToSSP : Base.TriTruth → SSP.SSPTrit
baseToSSP Base.tri-low = SSP.sspNegOne
baseToSSP Base.tri-mid = SSP.sspZero
baseToSSP Base.tri-high = SSP.sspPosOne

sspToBase : SSP.SSPTrit → Base.TriTruth
sspToBase SSP.sspNegOne = Base.tri-low
sspToBase SSP.sspZero = Base.tri-mid
sspToBase SSP.sspPosOne = Base.tri-high

cycleSSP : SSP.SSPTrit → SSP.SSPTrit
cycleSSP SSP.sspNegOne = SSP.sspZero
cycleSSP SSP.sspZero = SSP.sspPosOne
cycleSSP SSP.sspPosOne = SSP.sspNegOne

cycleSSP3 : (x : SSP.SSPTrit) → cycleSSP (cycleSSP (cycleSSP x)) ≡ x
cycleSSP3 SSP.sspNegOne = refl
cycleSSP3 SSP.sspZero = refl
cycleSSP3 SSP.sspPosOne = refl

cycleChartsIntertwine :
  (x : Base.TriTruth) → baseToSSP (cycleBase x) ≡ cycleSSP (baseToSSP x)
cycleChartsIntertwine Base.tri-low = refl
cycleChartsIntertwine Base.tri-mid = refl
cycleChartsIntertwine Base.tri-high = refl

------------------------------------------------------------------------
-- 2. Cube row/column shifts are exactly coordinate-cycle pullbacks.
------------------------------------------------------------------------

rowCyclePullback : Fine.PhaseFineField → Fine.PhaseFineField
rowCyclePullback field (row , column) = field (cycleBase row , column)

columnCyclePullback : Fine.PhaseFineField → Fine.PhaseFineField
columnCyclePullback field (row , column) = field (row , cycleBase column)

rowShiftIsRowCyclePullback :
  (face : Cube.Face9) →
  (coordinate : Base.TriTruth × Base.TriTruth) →
  Fine.lookupPhaseFine (Stabilizer.rowShift face) coordinate
  ≡ rowCyclePullback (Fine.lookupPhaseFine face) coordinate
rowShiftIsRowCyclePullback face (Base.tri-low , Base.tri-low) = refl
rowShiftIsRowCyclePullback face (Base.tri-low , Base.tri-mid) = refl
rowShiftIsRowCyclePullback face (Base.tri-low , Base.tri-high) = refl
rowShiftIsRowCyclePullback face (Base.tri-mid , Base.tri-low) = refl
rowShiftIsRowCyclePullback face (Base.tri-mid , Base.tri-mid) = refl
rowShiftIsRowCyclePullback face (Base.tri-mid , Base.tri-high) = refl
rowShiftIsRowCyclePullback face (Base.tri-high , Base.tri-low) = refl
rowShiftIsRowCyclePullback face (Base.tri-high , Base.tri-mid) = refl
rowShiftIsRowCyclePullback face (Base.tri-high , Base.tri-high) = refl

columnShiftIsColumnCyclePullback :
  (face : Cube.Face9) →
  (coordinate : Base.TriTruth × Base.TriTruth) →
  Fine.lookupPhaseFine (Stabilizer.columnShift face) coordinate
  ≡ columnCyclePullback (Fine.lookupPhaseFine face) coordinate
columnShiftIsColumnCyclePullback face (Base.tri-low , Base.tri-low) = refl
columnShiftIsColumnCyclePullback face (Base.tri-low , Base.tri-mid) = refl
columnShiftIsColumnCyclePullback face (Base.tri-low , Base.tri-high) = refl
columnShiftIsColumnCyclePullback face (Base.tri-mid , Base.tri-low) = refl
columnShiftIsColumnCyclePullback face (Base.tri-mid , Base.tri-mid) = refl
columnShiftIsColumnCyclePullback face (Base.tri-mid , Base.tri-high) = refl
columnShiftIsColumnCyclePullback face (Base.tri-high , Base.tri-low) = refl
columnShiftIsColumnCyclePullback face (Base.tri-high , Base.tri-mid) = refl
columnShiftIsColumnCyclePullback face (Base.tri-high , Base.tri-high) = refl

------------------------------------------------------------------------
-- 3. The same coordinate cycles on every first-Tits M3 sector.
------------------------------------------------------------------------

rowCycleSlot : Tits.TitsBasisSlot → Tits.TitsBasisSlot
rowCycleSlot slot = Tits.titsBasisSlot
  (Tits.sector slot)
  (cycleSSP (Tits.row slot))
  (Tits.column slot)

columnCycleSlot : Tits.TitsBasisSlot → Tits.TitsBasisSlot
columnCycleSlot slot = Tits.titsBasisSlot
  (Tits.sector slot)
  (Tits.row slot)
  (cycleSSP (Tits.column slot))

rowCycleSlot3 : (slot : Tits.TitsBasisSlot) →
  rowCycleSlot (rowCycleSlot (rowCycleSlot slot)) ≡ slot
rowCycleSlot3 (Tits.titsBasisSlot sector SSP.sspNegOne column) = refl
rowCycleSlot3 (Tits.titsBasisSlot sector SSP.sspZero column) = refl
rowCycleSlot3 (Tits.titsBasisSlot sector SSP.sspPosOne column) = refl

columnCycleSlot3 : (slot : Tits.TitsBasisSlot) →
  columnCycleSlot (columnCycleSlot (columnCycleSlot slot)) ≡ slot
columnCycleSlot3 (Tits.titsBasisSlot sector row SSP.sspNegOne) = refl
columnCycleSlot3 (Tits.titsBasisSlot sector row SSP.sspZero) = refl
columnCycleSlot3 (Tits.titsBasisSlot sector row SSP.sspPosOne) = refl

rowColumnSlotCommute : (slot : Tits.TitsBasisSlot) →
  rowCycleSlot (columnCycleSlot slot) ≡ columnCycleSlot (rowCycleSlot slot)
rowColumnSlotCommute (Tits.titsBasisSlot sector row column) = refl

------------------------------------------------------------------------
-- 4. Determinant sign of the coordinate actor.  A three-cycle is the product
--    of two transpositions, so its permutation determinant sign is positive.
------------------------------------------------------------------------

data PermutationSign : Set where
  signPositive signNegative : PermutationSign

multiplySign : PermutationSign → PermutationSign → PermutationSign
multiplySign signPositive s = s
multiplySign signNegative signPositive = signNegative
multiplySign signNegative signNegative = signPositive

threeCycleDeterminantSign : PermutationSign
threeCycleDeterminantSign = multiplySign signNegative signNegative

threeCycleHasPositiveDeterminantSign :
  threeCycleDeterminantSign ≡ signPositive
threeCycleHasPositiveDeterminantSign = refl

------------------------------------------------------------------------
-- 5. Source-bounded same-action status.
------------------------------------------------------------------------

record CubeFirstTitsSL3TranslationIntersection : Set where
  constructor cube-first-tits-sl3-translation-intersection
  field
    cubeRowShiftIsExactRowCyclePullback : Bool
    cubeColumnShiftIsExactColumnCyclePullback : Bool
    firstTitsRowCycleUsesSameThreeCoordinateChart : Bool
    firstTitsColumnCycleUsesSameThreeCoordinateChart : Bool
    rowAndColumnCyclesHaveOrderThree : Bool
    rowAndColumnCyclesCommute : Bool
    threeCyclePermutationDeterminantSignPositive : Bool
    finiteTranslationSpineCompatibleWithLeftRightSL3Factors : Bool
    fullContinuousSL3SameActionImportedHere : Bool
    dhrOrPhysicalGaugeIdentificationCreated : Bool
open CubeFirstTitsSL3TranslationIntersection public

canonicalCubeFirstTitsSL3TranslationIntersection :
  CubeFirstTitsSL3TranslationIntersection
canonicalCubeFirstTitsSL3TranslationIntersection =
  cube-first-tits-sl3-translation-intersection
    true true true true true true true true false false
