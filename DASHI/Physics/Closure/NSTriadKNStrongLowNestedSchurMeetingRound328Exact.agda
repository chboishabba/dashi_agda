module DASHI.Physics.Closure.NSTriadKNStrongLowNestedSchurMeetingRound328Exact where

------------------------------------------------------------------------
-- ROUND328 / STRONGLY-LOW HETEROCHIRAL-HH -> FINITE SCHUR MEETING POINT
--
-- The strongly-low inner-output subcone now owns:
--
--   R321--R323 : all four outer exponent thresholds are paid;
--   R326       : each literal paired inner Galerkin cell satisfies the
--                radical-free low-output physical bound.
--
-- Do NOT sum the inner cells first and estimate ||N_p||^2: that would recreate
-- a convolution-cardinality / coherent-Gram problem.  Keep the nested
-- (a,b;p,q) carrier and use R326 only as the cell majorant inside row/column
-- Schur aggregation.
--
-- This file therefore splits the remaining analytic producer into exactly two
-- domain receipts:
--
--   row Cauchy / row-budget receipt,
--   column aggregation / column-budget receipt.
--
-- Once both exist, the generic FiniteRowColumnSchurMeetingPointExact compiler
-- returns the squared operator bound.  No kernel cardinality is introduced by
-- this file.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Analysis.FiniteRowColumnSchurMeetingPointExact as Schur
import DASHI.Physics.Closure.NSTriadKNStrongLowPaysOuterHHRound323Exact as R323
import DASHI.Physics.Closure.NSTriadKNPhysicalInnerCommutatorLowOutputBoundRound326Exact as R326

record StrongLowNestedRowReceipt : Set where
  constructor strong-low-nested-row-receipt
  field
    outputMass rowBudget rowWeightedInput : ℚ
    rowBudgetNonnegative : 0ℚ ≤ rowBudget
    rowWeightedInputNonnegative : 0ℚ ≤ rowWeightedInput
    rowCauchyBound : outputMass ≤ rowBudget * rowWeightedInput

open StrongLowNestedRowReceipt public

record StrongLowNestedColumnReceipt : Set where
  constructor strong-low-nested-column-receipt
  field
    rowWeightedInput columnBudget inputMass : ℚ
    columnBudgetNonnegative : 0ℚ ≤ columnBudget
    inputMassNonnegative : 0ℚ ≤ inputMass
    rowWeightedInputNonnegative : 0ℚ ≤ rowWeightedInput
    columnAggregationBound : rowWeightedInput ≤ columnBudget * inputMass

open StrongLowNestedColumnReceipt public

record StrongLowNestedSchurData : Set where
  constructor strong-low-nested-schur-data
  field
    row : StrongLowNestedRowReceipt
    column : StrongLowNestedColumnReceipt
    weightedInputAgrees :
      rowWeightedInput row ≡ rowWeightedInput column

open StrongLowNestedSchurData public

asGenericSchurReceipt :
  (D : StrongLowNestedSchurData) →
  Schur.FiniteRowColumnSchurReceipt
asGenericSchurReceipt D =
  let
    R = row D
    C = column D
  in
  Schur.finite-row-column-schur-receipt
    (outputMass R)
    (rowBudget R)
    (rowWeightedInput R)
    (columnBudget C)
    (inputMass C)
    (rowBudgetNonnegative R)
    (columnBudgetNonnegative C)
    (inputMassNonnegative C)
    (rowWeightedInputNonnegative R)
    (rowCauchyBound R)
    (substWeightedColumn D)
  where
  substWeightedColumn :
    (D' : StrongLowNestedSchurData) →
    rowWeightedInput (row D')
    ≤ columnBudget (column D') * inputMass (column D')
  substWeightedColumn D' rewrite weightedInputAgrees D' =
    columnAggregationBound (column D')

strongLowNestedSchurSquaredBound :
  (D : StrongLowNestedSchurData) →
  outputMass (row D)
  ≤ (rowBudget (row D) * columnBudget (column D))
      * inputMass (column D)
strongLowNestedSchurSquaredBound D =
  Schur.finiteRowColumnSchurSquaredBound (asGenericSchurReceipt D)

round328AllOuterExponentThresholdsAlreadyPaid : Bool
round328AllOuterExponentThresholdsAlreadyPaid =
  R323.round323StronglyLowPaysAllFourHeterochiralHHOuterExponentCells

round328PhysicalInnerCellMajorantAlreadyClosed : Bool
round328PhysicalInnerCellMajorantAlreadyClosed =
  R326.round326PhysicalR120R178SameObjectBoundClosed

round328NaiveInnerNormSquareSummationUsed : Bool
round328NaiveInnerNormSquareSummationUsed = false

round328NestedRowReceiptClosed : Bool
round328NestedRowReceiptClosed = false

round328NestedColumnReceiptClosed : Bool
round328NestedColumnReceiptClosed = false

round328StrongLowNestedSchurClosed : Bool
round328StrongLowNestedSchurClosed = false

round328SpacetimePaid : Bool
round328SpacetimePaid = false

round328PackageAClosed : Bool
round328PackageAClosed = false

round328ClayPromotion : Bool
round328ClayPromotion = false

round328PackageAClosedIsFalse : round328PackageAClosed ≡ false
round328PackageAClosedIsFalse = refl

round328ClayPromotionIsFalse : round328ClayPromotion ≡ false
round328ClayPromotionIsFalse = refl
