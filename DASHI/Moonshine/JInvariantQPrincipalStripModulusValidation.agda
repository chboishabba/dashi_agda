module DASHI.Moonshine.JInvariantQPrincipalStripModulusValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as P

------------------------------------------------------------------------
-- RED owner: the literal q(tau)=exp(2*pi*i*tau) producer must inherit the
-- principal-strip exponential modulus theorem without changing carriers.
------------------------------------------------------------------------

qExponentRegression :
  (C : Complex.ConstructedComplexPackage) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  Q.qOf C tau
  ≡ Complex.expC (Complex.complexExponential C) (P.qExponent C tau)
qExponentRegression = P.qOfIsExponentialOfQExponent

qPrincipalStripModulusRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (P0 : Polar.OrdinaryPolarData C D F)
    (B : Polar.OrdinaryPrincipalBranchLaws C D F P0)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (strip : Polar.PrincipalStrip P0 (P.qExponent C tau)) →
  Polar.modulus F (Q.qOf C tau)
  ≡ Real.exp (Real.exponential (Complex.realPackage C))
      (Complex.re (P.qExponent C tau))
qPrincipalStripModulusRegression = P.qModulusOnPrincipalStrip

qBelowOneFromNegativeExponentRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (P0 : Polar.OrdinaryPolarData C D F)
    (B : Polar.OrdinaryPrincipalBranchLaws C D F P0)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (strip : Polar.PrincipalStrip P0 (P.qExponent C tau)) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Complex.re (P.qExponent C tau))
    (Real.zero (Real.real (Complex.realPackage C))) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Polar.modulus F (Q.qOf C tau))
    (Real.one (Real.real (Complex.realPackage C)))
qBelowOneFromNegativeExponentRegression =
  P.qModulusBelowOneFromNegativeRealPart
