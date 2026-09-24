module DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusValidation where

import Real as BishopReal
import Sequence as BishopSequence
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as Majorant
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as P

upperHalfPlaneRadiusRegression :
  ∀ {piB imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ piB →
  BishopReal._<_ BishopReal.0ℝ imag →
  Unit.BishopUnitIntervalRatio (P.qRadius piB imag)
upperHalfPlaneRadiusRegression = P.qRadiusUnitInterval

machinRadiusRegression :
  ∀ {imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ imag →
  Unit.BishopUnitIntervalRatio (P.machinQRadius imag)
machinRadiusRegression = P.machinQRadiusUnitInterval

machinE4MajorantRegression :
  ∀ {imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ imag →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Majorant.e4MajorantTerm (P.machinQRadius imag))
machinE4MajorantRegression =
  P.machinE4MajorantAbsoluteConvergence

machinE6MajorantRegression :
  ∀ {imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ imag →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Majorant.e6MajorantTerm (P.machinQRadius imag))
machinE6MajorantRegression =
  P.machinE6MajorantAbsoluteConvergence
