module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineCellularH2Exact where

------------------------------------------------------------------------
-- EXACT TWO-CELL H^2 MODEL FOR CP^1 ~= S^2
--
-- The standard CW decomposition of S^2 has one 0-cell, no 1-cells, one
-- 2-cell, and no 3-cells. With rational coefficients, the degree-two
-- cochain group is therefore Q and both adjacent coboundaries are zero.
--
-- This module computes that cellular degree-two cohomology exactly and welds
-- its unit generator to the already-constructed finite P^1 H^(1,1) model.
--
-- It does NOT identify this finite cellular calculation with singular
-- cohomology of the literal topological CP^1. That cellular/singular
-- comparison is the remaining honest topological theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineCycleClassExact as P1

record CP1CellularDegreeTwoCochain : Set where
  constructor cellular2
  field
    coefficient : ℚ

open CP1CellularDegreeTwoCochain public

cellularZero : CP1CellularDegreeTwoCochain
cellularZero = cellular2 0ℚ

cellularAdd :
  CP1CellularDegreeTwoCochain →
  CP1CellularDegreeTwoCochain →
  CP1CellularDegreeTwoCochain
cellularAdd (cellular2 left) (cellular2 right) =
  cellular2 (left + right)

cellularScale :
  ℚ →
  CP1CellularDegreeTwoCochain →
  CP1CellularDegreeTwoCochain
cellularScale scalar (cellular2 value) =
  cellular2 (scalar * value)

degreeOneCoboundary :
  ⊤ → CP1CellularDegreeTwoCochain
degreeOneCoboundary tt = cellularZero

degreeTwoCoboundary :
  CP1CellularDegreeTwoCochain → ⊤
degreeTwoCoboundary cochain = tt

degreeTwoClosed : ∀ cochain →
  degreeTwoCoboundary cochain ≡ tt
degreeTwoClosed cochain = refl

degreeTwoBoundariesAreZero : ∀ degreeOne →
  degreeOneCoboundary degreeOne ≡ cellularZero
degreeTwoBoundariesAreZero tt = refl

CP1CellularH2 : Set
CP1CellularH2 = ℚ

cochainToH2 : CP1CellularDegreeTwoCochain → CP1CellularH2
cochainToH2 (cellular2 value) = value

h2ToCochain : CP1CellularH2 → CP1CellularDegreeTwoCochain
h2ToCochain value = cellular2 value

cochainH2LeftInverse : ∀ cochain →
  h2ToCochain (cochainToH2 cochain) ≡ cochain
cochainH2LeftInverse (cellular2 value) = refl

cochainH2RightInverse : ∀ value →
  cochainToH2 (h2ToCochain value) ≡ value
cochainH2RightInverse value = refl

cellularPointGenerator : CP1CellularH2
cellularPointGenerator = 1ℚ

everyCellularH2ClassIsPointMultiple : ∀ value →
  value ≡ value * cellularPointGenerator
everyCellularH2ClassIsPointMultiple value =
  solve (value ∷ [])

p1H11ToCellularH2 :
  P1.P1RationalH11Class → CP1CellularH2
p1H11ToCellularH2 (P1.h11Class value) = value

cellularH2ToP1H11 :
  CP1CellularH2 → P1.P1RationalH11Class
cellularH2ToP1H11 value = P1.h11Class value

p1H11CellularLeftInverse : ∀ h11 →
  cellularH2ToP1H11 (p1H11ToCellularH2 h11) ≡ h11
p1H11CellularLeftInverse (P1.h11Class value) = refl

p1H11CellularRightInverse : ∀ value →
  p1H11ToCellularH2 (cellularH2ToP1H11 value) ≡ value
p1H11CellularRightInverse value = refl

pointCycleClassWeldsToCellularGenerator :
  p1H11ToCellularH2
    (P1.p1CycleClass P1.pointCycle)
  ≡ cellularPointGenerator
pointCycleClassWeldsToCellularGenerator = refl

everyCellularClassHasPointCycle : ∀ value →
  p1H11ToCellularH2
    (P1.p1CycleClass
      (P1.scaleDivisorCycle value P1.pointCycle))
  ≡ value
everyCellularClassHasPointCycle value =
  solve (value ∷ [])
