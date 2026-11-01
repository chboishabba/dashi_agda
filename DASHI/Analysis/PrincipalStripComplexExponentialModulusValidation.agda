module DASHI.Analysis.PrincipalStripComplexExponentialModulusValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Analysis.PrincipalStripComplexExponentialModulusExact as P

------------------------------------------------------------------------
-- RED owner: the existing principal-log inverse law must determine the modulus
-- of exp(z) on the principal strip without importing a Pythagorean theorem.
------------------------------------------------------------------------

principalStripExponentialModulusRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (P0 : Polar.OrdinaryPolarData C D F)
    (B : Polar.OrdinaryPrincipalBranchLaws C D F P0)
    (z : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (strip : Polar.PrincipalStrip P0 z) →
  Polar.modulus F (Complex.expC (Complex.complexExponential C) z)
  ≡ Real.exp (Real.exponential (Complex.realPackage C)) (Complex.re z)
principalStripExponentialModulusRegression =
  P.exponentialModulusOnPrincipalStrip
