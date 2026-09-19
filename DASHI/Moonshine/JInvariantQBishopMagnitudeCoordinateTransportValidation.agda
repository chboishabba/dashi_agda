module DASHI.Moonshine.JInvariantQBishopMagnitudeCoordinateTransportValidation where

import Real as BishopReal

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.JInvariantQBishopExponentTransportCompilerExact as Exponent
import DASHI.Moonshine.JInvariantQBishopMagnitudeCoordinateTransportExact as P

magnitudeCoordinateCompilerRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ} →
  P.QBishopMagnitudeCoordinateTransport C tau piB imagB →
  Exponent.QBishopExponentMagnitudeTransport C tau piB imagB
magnitudeCoordinateCompilerRegression =
  P.compileExponentMagnitudeTransport
