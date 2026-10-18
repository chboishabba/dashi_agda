module DASHI.Analysis.PrincipalStripComplexExponentialModulusExact where

------------------------------------------------------------------------
-- PRINCIPAL-STRIP COMPLEX EXPONENTIAL MODULUS
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- `OrdinaryComplexPolar` already owns a principal logarithm whose real
-- component is the real logarithm of the complex modulus, together with the
-- exact inverse law
--
--   principalLog (expC z) = z
--
-- on the admitted principal strip.  Taking real components therefore gives
--
--   log |expC z| = Re z.
--
-- The existing real exp/log inverse then yields
--
--   |expC z| = exp (Re z).
--
-- This proof deliberately avoids sin^2+cos^2=1.  It therefore does not depend
-- on the still-unpaid classical/Bishop trigonometric same-object weld.
--
-- The theorem is strip-local: no global branch claim is manufactured.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar

exponentialModulusOnPrincipalStrip :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (P : Polar.OrdinaryPolarData C D F)
    (B : Polar.OrdinaryPrincipalBranchLaws C D F P)
    (z : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (strip : Polar.PrincipalStrip P z) →
  Polar.modulus F (Complex.expC (Complex.complexExponential C) z)
  ≡ Real.exp (Real.exponential (Complex.realPackage C)) (Complex.re z)
exponentialModulusOnPrincipalStrip {C} {D} {F} P B z strip =
  let
    E = Real.exponential (Complex.realPackage C)
    L = Real.logarithm (Complex.realPackage C)
    CE = Complex.complexExponential C
    expZ = Complex.expC CE z
    expZDomain = Polar.exponentialInDomain P z strip
    modulusPos = Polar.modulusPositive P expZ expZDomain

    logModulusIsRealPart :
      Real.log L (Polar.modulus F expZ) modulusPos ≡ Complex.re z
    logModulusIsRealPart =
      cong Complex.re (Polar.principalLogOfExponential B z strip)
  in
  trans
    (sym (Real.expLog L (Polar.modulus F expZ) modulusPos))
    (cong (Real.exp E) logModulusIsRealPart)

------------------------------------------------------------------------
-- Explicit authority boundary.
------------------------------------------------------------------------

record PrincipalStripExponentialModulusBoundary : Set where
  constructor principal-strip-exponential-modulus-boundary
  field
    existingPrincipalLogReused : Bool
    existingPrincipalInverseLawReused : Bool
    existingRealExpLogInverseReused : Bool
    sameConcreteComplexCarrierRetained : Bool
    pythagoreanIdentityRequired : Bool
    classicalTrigSameObjectWeldRequired : Bool
    globalBranchFreeModulusLawClaimed : Bool
    reading : String

open PrincipalStripExponentialModulusBoundary public

canonicalPrincipalStripExponentialModulusBoundary :
  PrincipalStripExponentialModulusBoundary
canonicalPrincipalStripExponentialModulusBoundary =
  principal-strip-exponential-modulus-boundary
    true true true true
    false false false
    "on the existing principal strip, principalLog(exp z)=z plus real exp/log inversion derives |exp z|=exp(Re z) on the same ConcreteComplex carrier; no Pythagorean or global branch theorem is imported"
