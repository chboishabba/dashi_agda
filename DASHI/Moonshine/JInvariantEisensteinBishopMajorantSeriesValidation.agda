module DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesValidation where

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as P

e4MajorantAbsoluteConvergenceRegression :
  ∀ {ratio : BishopReal.ℝ} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (P.e4MajorantTerm ratio)
e4MajorantAbsoluteConvergenceRegression =
  P.e4MajorantAbsoluteConvergence

e6MajorantAbsoluteConvergenceRegression :
  ∀ {ratio : BishopReal.ℝ} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (P.e6MajorantTerm ratio)
e6MajorantAbsoluteConvergenceRegression =
  P.e6MajorantAbsoluteConvergence
