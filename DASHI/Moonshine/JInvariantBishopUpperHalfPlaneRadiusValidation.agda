module DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusValidation where

import Real as BishopReal
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
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
