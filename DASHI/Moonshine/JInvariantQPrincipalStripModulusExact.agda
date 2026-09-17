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
-- This owner does not yet normalize the real part to -2*pi*Im(tau), prove the
-- strip condition from a modular fundamental-domain hypothesis, or derive the
-- strict inequality |q|<1.  Those are kept as separate order/algebra seams.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

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
    qExponentRealPartNormalized : Bool
    principalStripDerivedFromFundamentalDomain : Bool
    qAbsoluteValueLessThanOneDerived : Bool
    reading : String

open QPrincipalStripModulusBoundary public

canonicalQPrincipalStripModulusBoundary : QPrincipalStripModulusBoundary
canonicalQPrincipalStripModulusBoundary =
  q-principal-strip-modulus-boundary
    true true true
    false
    false false false
    "the literal q producer now has |q(tau)|=exp(Re((2*pi*i)tau)) on the existing principal strip without Pythagorean input; remaining debt is real-part normalization, strip-domain payment, and strict real-order decay"
