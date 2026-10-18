module DASHI.Moonshine.JInvariantQUpperHalfPlaneDecayCompilerValidation where

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as FiniteQ
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as QModulus
import DASHI.Moonshine.JInvariantQUpperHalfPlaneDecayCompilerExact as P

------------------------------------------------------------------------
-- RED owner: exact Cartesian normalization + minimal strict-order laws should
-- turn Im(tau)>0 into a negative q-exponent real part, and hence |q|<1 on the
-- existing principal strip.
------------------------------------------------------------------------

upperHalfPlaneNegativeExponentRegression :
  ∀ {C : Complex.ConstructedComplexPackage} →
  (N : Ring.ConstructedRealRingNormalisationLaws
    (Real.real (Complex.realPackage C))) →
  (O : P.QUpperHalfPlaneOrderLaws C) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Real.zero (Real.real (Complex.realPackage C)))
    (Complex.im tau) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Complex.re (QModulus.qExponent C tau))
    (Real.zero (Real.real (Complex.realPackage C)))
upperHalfPlaneNegativeExponentRegression =
  P.upperHalfPlaneGivesNegativeQExponentRealPart

upperHalfPlaneQDecayRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (N : Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C)))
    (O : P.QUpperHalfPlaneOrderLaws C)
    (polar : Polar.OrdinaryPolarData C D F)
    (branch : Polar.OrdinaryPrincipalBranchLaws C D F polar)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (strip : Polar.PrincipalStrip polar (QModulus.qExponent C tau)) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Real.zero (Real.real (Complex.realPackage C)))
    (Complex.im tau) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Polar.modulus F (FiniteQ.qOf C tau))
    (Real.one (Real.real (Complex.realPackage C)))
upperHalfPlaneQDecayRegression = P.upperHalfPlaneQBelowOneOnPrincipalStrip
