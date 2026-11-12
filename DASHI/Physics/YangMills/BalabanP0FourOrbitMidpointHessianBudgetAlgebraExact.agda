module DASHI.Physics.YangMills.BalabanP0FourOrbitMidpointHessianBudgetAlgebraExact where

-- Exact source-matched rational MIDPOINT/HESSIAN ERROR NORMALISATION.
--
-- A 4D original unit-normalised box is of side 1/2 in x coordinates.
-- 4 directional midpoint errors times h^2 / 24 times dx box volume
-- (1/16) give M2 / 384 on the x chart.
-- The physical Fourier measure d^4p/(2pi)^4 = dx/16 adds a
-- FURTHER factor 1/16: M2 / 6144 per individual physical cell.
--
-- Original outer-rank orbit cardinalities are 64,96,64,16, and so
-- the normalised physical four-orbit Hessian budget is
--       (4*M1 + 6*M2 + 4*M3 + M4)/384.
--
-- These are EXACT finite rational algebraic theorems.
-- To turn them into analytic QUADRATURE error certificates, an
-- original source-specific uniform Hessian bound and a genuine
-- multidimensional midpoint theorem are REQUIRED. This file does
-- not inhabit Eval.CertifiedBoxQuadrature's abstract Set fields or
-- fabricate physical integral values.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4SemanticFourRepresentativeQuadratureExact as Four
import DASHI.Physics.YangMills.BalabanClayT4AuxiliaryWilsonNormalizedMeasureExact as Norm

oneCellMidpointRationalHessianCoefficient : ℚ
oneCellMidpointRationalHessianCoefficient =
  (((+ 4 / 1) * ((+ 1 / 2) * (+ 1 / 2)))
    * (+ 1 / 24)) * (+ 1 / 16)

oneCellMidpointCoefficientExact :
  oneCellMidpointRationalHessianCoefficient ≡ (+ 1 / 384)
oneCellMidpointCoefficientExact = Ring.solve-∀

onePhysicalCellHessianError : ℚ → ℚ
onePhysicalCellHessianError m =
  Norm.brillouinUnitVolumeFactor *
    (oneCellMidpointRationalHessianCoefficient * m)

onePhysicalCellCoefficientExact :
  ∀ m →
  onePhysicalCellHessianError m ≡ (+ 1 / 6144) * m
onePhysicalCellCoefficientExact m = Ring.solve-∀ m

fourRankPhysicalHessianError :
  (m1 m2 m3 m4 : ℚ) → ℚ
fourRankPhysicalHessianError m1 m2 m3 m4 =
  (+ 64 / 1) * onePhysicalCellHessianError m1
  + (+ 96 / 1) * onePhysicalCellHessianError m2
  + (+ 64 / 1) * onePhysicalCellHessianError m3
  + (+ 16 / 1) * onePhysicalCellHessianError m4

fourRankHessianOrbitCollapseExact :
  ∀ m1 m2 m3 m4 →
  fourRankPhysicalHessianError m1 m2 m3 m4
  ≡
  (((+ 4 / 1) * m1
    + (+ 6 / 1) * m2
    + (+ 4 / 1) * m3
    + m4) * (+ 1 / 384))
fourRankHessianOrbitCollapseExact m1 m2 m3 m4 =
  Ring.solve-∀ m1 m2 m3 m4

-- Actual input numbers from the original source four quadrature records.
-- No replacement proxy M_i values are introduced.
actualFourHessianBudget :
  ∀ {scalarData} →
  Four.LiteralSemanticFourQuadratureCut scalarData → ℚ
actualFourHessianBudget dataSet =
  fourRankPhysicalHessianError
    (Eval.hessianNormUpper (Four.quadrature1 dataSet))
    (Eval.hessianNormUpper (Four.quadrature2 dataSet))
    (Eval.hessianNormUpper (Four.quadrature3 dataSet))
    (Eval.hessianNormUpper (Four.quadrature4 dataSet))

actualFourHessianBudgetExact :
  ∀ {scalarData} →
  (dataSet : Four.LiteralSemanticFourQuadratureCut scalarData) →
  actualFourHessianBudget dataSet
  ≡
  (((+ 4 / 1) * Eval.hessianNormUpper (Four.quadrature1 dataSet)
    + (+ 6 / 1) * Eval.hessianNormUpper (Four.quadrature2 dataSet)
    + (+ 4 / 1) * Eval.hessianNormUpper (Four.quadrature3 dataSet)
    + Eval.hessianNormUpper (Four.quadrature4 dataSet))
    * (+ 1 / 384))
actualFourHessianBudgetExact dataSet =
  fourRankHessianOrbitCollapseExact
    (Eval.hessianNormUpper (Four.quadrature1 dataSet))
    (Eval.hessianNormUpper (Four.quadrature2 dataSet))
    (Eval.hessianNormUpper (Four.quadrature3 dataSet))
    (Eval.hessianNormUpper (Four.quadrature4 dataSet))

-- Analytic gate remains precisely:
-- - all four source hessianNormUpper prove a TRUE upper bound on
--   Hessian directional second derivatives of the SAME physical scalar;
-- - the source midpoints are real values of the same regularIntegrand;
-- - the real integral obeys the 4D midpoint remainder theorem;
-- - source error covariance under the stabilizer or full B4 action.
