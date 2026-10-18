module DASHI.Moonshine.JInvariantQPrincipalStripModulusExact where

------------------------------------------------------------------------
-- LITERAL q(tau) PRINCIPAL-STRIP MODULUS
--
-- Reuse the exact exponent expression already owned by
-- `JInvariantEisensteinFiniteQSeriesExact.qOf`:
--
--   q(tau) = expC ((2 * (i*pi)) * tau).
--
-- The generic principal-strip exponential-modulus theorem then gives
--
--   |q(tau)| = exp (Re ((2*pi*i) tau))
--
-- whenever that exact exponent lies in the existing principal strip.
--
-- Once the real part of that exponent is proved negative, the already-owned
-- strict monotonicity and exp(0)=1 laws discharge |q|<1 directly.  This owner
-- still does not normalize Re((2*pi*i)tau) to -2*pi*Im(tau) or derive the strip
-- condition from a modular fundamental-domain hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Analysis.PrincipalStripComplexExponentialModulusExact as Modulus
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q

qExponent :
  (C : Complex.ConstructedComplexPackage) →
  Complex.ComplexPair (Real.real (Complex.realPackage C)) →
  Complex.ComplexPair (Real.real (Complex.realPackage C))
qExponent C tau =
  let
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C
    piC = Complex.complex (Complex.pi CE) (Real.zero R)
    twoPiI = Q.scaleNatC 2 (Complex._*C_ Complex.imaginaryUnit piC)
  in
  Complex._*C_ twoPiI tau

qOfIsExponentialOfQExponent :
  (C : Complex.ConstructedComplexPackage) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  Q.qOf C tau
  ≡ Complex.expC (Complex.complexExponential C) (qExponent C tau)
qOfIsExponentialOfQExponent C tau = refl

qModulusOnPrincipalStrip :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (P : Polar.OrdinaryPolarData C D F)
    (B : Polar.OrdinaryPrincipalBranchLaws C D F P)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (strip : Polar.PrincipalStrip P (qExponent C tau)) →
  Polar.modulus F (Q.qOf C tau)
  ≡ Real.exp (Real.exponential (Complex.realPackage C))
      (Complex.re (qExponent C tau))
qModulusOnPrincipalStrip {C} {D} {F} P B tau strip =
  Modulus.exponentialModulusOnPrincipalStrip
    P B (qExponent C tau) strip

qModulusBelowOneFromNegativeRealPart :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (P : Polar.OrdinaryPolarData C D F)
    (B : Polar.OrdinaryPrincipalBranchLaws C D F P)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (strip : Polar.PrincipalStrip P (qExponent C tau)) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Complex.re (qExponent C tau))
    (Real.zero (Real.real (Complex.realPackage C))) →
  Real._<_ (Real.real (Complex.realPackage C))
    (Polar.modulus F (Q.qOf C tau))
    (Real.one (Real.real (Complex.realPackage C)))
qModulusBelowOneFromNegativeRealPart {C} {D} {F} P B tau strip negative =
  let
    R = Real.real (Complex.realPackage C)
    E = Real.exponential (Complex.realPackage C)
    modulusEqualsExp = qModulusOnPrincipalStrip P B tau strip
    expNegativeBelowExpZero = Real.expStrictMonotone E negative
    expNegativeBelowOne =
      subst
        (λ upper → Real._<_ R (Real.exp E (Complex.re (qExponent C tau))) upper)
        (Real.expZero E)
        expNegativeBelowExpZero
  in
  subst
    (λ lower → Real._<_ R lower (Real.one R))
    (sym modulusEqualsExp)
    expNegativeBelowOne

------------------------------------------------------------------------
-- Exact frontier after the principal-log route.
------------------------------------------------------------------------

record QPrincipalStripModulusBoundary : Set where
  constructor q-principal-strip-modulus-boundary
  field
    existingQProducerReused : Bool
    exactQExponentFactored : Bool
    principalLogModulusCompilerReused : Bool
    pythagoreanRequiredForQModulus : Bool
    negativeRealPartImpliesQBelowOne : Bool
    qExponentRealPartNormalized : Bool
    principalStripDerivedFromFundamentalDomain : Bool
    upperHalfPlaneImpliesNegativeExponentRealPart : Bool
    reading : String

open QPrincipalStripModulusBoundary public

canonicalQPrincipalStripModulusBoundary : QPrincipalStripModulusBoundary
canonicalQPrincipalStripModulusBoundary =
  q-principal-strip-modulus-boundary
    true true true
    false
    true
    false false false
    "the literal q producer now has |q(tau)|=exp(Re((2*pi*i)tau)) on the existing principal strip and negative exponent real part implies |q|<1 using only exp monotonicity and exp(0)=1; remaining debt is real-part normalization and the domain/order payment from the intended upper-half-plane chart"
