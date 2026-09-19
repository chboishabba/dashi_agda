module DASHI.Moonshine.JInvariantLiteralQBishopRadiusSameObjectReductionValidation where

import Real as BishopReal

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as FiniteQ
import DASHI.Moonshine.JInvariantEisensteinBishopRadiusWeldExact as RadiusWeld
import DASHI.Moonshine.JInvariantQBishopExponentTransportCompilerExact as Exponent
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as BishopRadius
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as BishopExp
import DASHI.Moonshine.JInvariantLiteralQBishopRadiusSameObjectReductionExact as P

literalRadiusReductionRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (polar : Polar.OrdinaryPolarData C D F)
    (branch : Polar.OrdinaryPrincipalBranchLaws C D F polar)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ}
    (transport : P.LiteralQBishopRadiusTransport C tau piB imagB)
    (strip : Polar.PrincipalStrip polar (P.qExponent C tau))
    (piPositive : BishopReal._<_ BishopReal.0ℝ piB)
    (imagPositive : BishopReal._<_ BishopReal.0ℝ imagB) →
  RadiusWeld.LiteralRadiusBishopWeld
    (P.LegacyRadiusRelation transport)
    (Polar.modulus F (FiniteQ.qOf C tau))
literalRadiusReductionRegression =
  P.compileLiteralQRadiusWeld

transportConstructorRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    (N : Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C)))
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ}
    (magnitude :
      Exponent.QBishopExponentMagnitudeTransport C tau piB imagB) →
  (Exponent.toLegacy magnitude
      (BishopExp.bishopExp
        (BishopReal.-_
          (BishopRadius.qExponentMagnitude piB imagB)))
    ≡
    Real.exp
      (Real.exponential (Complex.realPackage C))
      (Exponent.toLegacy magnitude
        (BishopReal.-_
          (BishopRadius.qExponentMagnitude piB imagB)))) →
  P.LiteralQBishopRadiusTransport C tau piB imagB
transportConstructorRegression =
  P.transportFromMagnitudeAndExponential
