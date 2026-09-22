module DASHI.Moonshine.EisensteinCoefficientMajorantExact where

------------------------------------------------------------------------
-- E4/E6 COEFFICIENT TERMS -> REAL POLYNOMIAL-GEOMETRIC MAJORANTS
--
-- With the executable divisor sums now internal:
--
--   sigma_3(n) <= n^4
--   sigma_5(n) <= n^6.
--
-- For r = |q| and any submultiplicative complex norm compatible with natural
-- scaling, the literal q-series terms satisfy
--
--   |240 sigma_3(n) q^n| <= 240 n^4 r^n,
--   |504 sigma_5(n) q^n| <= 504 n^6 r^n.
--
-- This module compiles that reduction.  The remaining summability theorem is
-- purely real: polynomial times geometric with 0 <= r < 1.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q

private
  RealCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  RealCarrier C = Real.Real (Real.real (Complex.realPackage C))

  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  ComplexCarrier C = Complex.ComplexPair (Real.real (Complex.realPackage C))

------------------------------------------------------------------------
-- 1. Natural scaling on the selected real carrier.
------------------------------------------------------------------------

scaleNatR :
  ∀ {C : Complex.ConstructedComplexPackage} →
  Nat → RealCarrier C → RealCarrier C
scaleNatR {C} zero x =
  Real.zero (Real.real (Complex.realPackage C))
scaleNatR {C} (suc n) x =
  Real._+_
    (Real.real (Complex.realPackage C))
    x
    (scaleNatR {C} n x)

powR :
  ∀ {C : Complex.ConstructedComplexPackage} →
  RealCarrier C → Nat → RealCarrier C
powR {C} x zero =
  Real.one (Real.real (Complex.realPackage C))
powR {C} x (suc n) =
  Real._*_
    (Real.real (Complex.realPackage C))
    x
    (powR {C} x n)

------------------------------------------------------------------------
-- 2. Minimal complex-norm compatibility needed by the coefficient reduction.
------------------------------------------------------------------------

record ComplexQSeriesNormLaws
    (C : Complex.ConstructedComplexPackage) : Set₁ where

  private
    R = Real.real (Complex.realPackage C)

  field
    norm : ComplexCarrier C → RealCarrier C

    normPower :
      (z : ComplexCarrier C) →
      (n : Nat) →
      norm (Q.powC z n) ≡ powR {C} (norm z) n

    normNaturalScale :
      (m : Nat) →
      (z : ComplexCarrier C) →
      norm (Q.scaleNatC m z)
      ≡ scaleNatR {C} m (norm z)

    scaleNatMonotoneCoefficient :
      ∀ {left right : Nat} →
      left ≤ right →
      (x : RealCarrier C) →
      Real._≤_ R
        (scaleNatR {C} left x)
        (scaleNatR {C} right x)

open ComplexQSeriesNormLaws public

------------------------------------------------------------------------
-- 3. Scalar majorants.
------------------------------------------------------------------------

e4PolynomialCoefficient : Nat → Nat
e4PolynomialCoefficient n =
  240 * Hecke.powNat n 4

e6PolynomialCoefficient : Nat → Nat
e6PolynomialCoefficient n =
  504 * Hecke.powNat n 6

e4ScalarMajorant :
  ∀ {C : Complex.ConstructedComplexPackage} →
  RealCarrier C → Nat → RealCarrier C
e4ScalarMajorant {C} r n =
  scaleNatR {C}
    (e4PolynomialCoefficient n)
    (powR {C} r n)

e6ScalarMajorant :
  ∀ {C : Complex.ConstructedComplexPackage} →
  RealCarrier C → Nat → RealCarrier C
e6ScalarMajorant {C} r n =
  scaleNatR {C}
    (e6PolynomialCoefficient n)
    (powR {C} r n)

------------------------------------------------------------------------
-- 4. Literal complex q-series terms.
------------------------------------------------------------------------

e4Term :
  (C : Complex.ConstructedComplexPackage) →
  Nat →
  ComplexCarrier C →
  ComplexCarrier C
e4Term C n tau =
  Q.scaleNatC
    (240 * Q.sigma3 Q.canonicalDivisorPowerKernel n)
    (Q.powC (Q.qOf C tau) n)

e6Term :
  (C : Complex.ConstructedComplexPackage) →
  Nat →
  ComplexCarrier C →
  ComplexCarrier C
e6Term C n tau =
  Q.scaleNatC
    (504 * Q.sigma5 Q.canonicalDivisorPowerKernel n)
    (Q.powC (Q.qOf C tau) n)

------------------------------------------------------------------------
-- 5. Natural coefficient inequalities.
------------------------------------------------------------------------

e4CoefficientBound :
  (n : Nat) →
  240 * Q.sigma3 Q.canonicalDivisorPowerKernel n
  ≤ e4PolynomialCoefficient n
e4CoefficientBound n =
  Data.Nat.Properties.*-mono-≤
    Data.Nat.Properties.≤-refl
    (Q.canonicalSigma3QuarticBound n)

e6CoefficientBound :
  (n : Nat) →
  504 * Q.sigma5 Q.canonicalDivisorPowerKernel n
  ≤ e6PolynomialCoefficient n
e6CoefficientBound n =
  Data.Nat.Properties.*-mono-≤
    Data.Nat.Properties.≤-refl
    (Q.canonicalSigma5SexticBound n)

------------------------------------------------------------------------
-- 6. Main majorant theorems.
------------------------------------------------------------------------

e4TermMajorized :
  ∀ {C} →
  (laws : ComplexQSeriesNormLaws C) →
  (tau : ComplexCarrier C) →
  (n : Nat) →
  Real._≤_
    (Real.real (Complex.realPackage C))
    (norm laws (e4Term C n tau))
    (e4ScalarMajorant {C} (norm laws (Q.qOf C tau)) n)
e4TermMajorized laws tau n
  rewrite normNaturalScale laws
    (240 * Q.sigma3 Q.canonicalDivisorPowerKernel n)
    (Q.powC (Q.qOf _ tau) n)
  | normPower laws (Q.qOf _ tau) n =
  scaleNatMonotoneCoefficient laws
    (e4CoefficientBound n)
    (powR (norm laws (Q.qOf _ tau)) n)

e6TermMajorized :
  ∀ {C} →
  (laws : ComplexQSeriesNormLaws C) →
  (tau : ComplexCarrier C) →
  (n : Nat) →
  Real._≤_
    (Real.real (Complex.realPackage C))
    (norm laws (e6Term C n tau))
    (e6ScalarMajorant {C} (norm laws (Q.qOf C tau)) n)
e6TermMajorized laws tau n
  rewrite normNaturalScale laws
    (504 * Q.sigma5 Q.canonicalDivisorPowerKernel n)
    (Q.powC (Q.qOf _ tau) n)
  | normPower laws (Q.qOf _ tau) n =
  scaleNatMonotoneCoefficient laws
    (e6CoefficientBound n)
    (powR (norm laws (Q.qOf _ tau)) n)

------------------------------------------------------------------------
-- 7. Remaining real theorem interface.
------------------------------------------------------------------------

record PolynomialGeometricSummability
    (C : Complex.ConstructedComplexPackage)
    (r : RealCarrier C) : Set₁ where
  field
    Nonnegative : RealCarrier C → Set
    BelowOne : RealCarrier C → Set

    rNonnegative : Nonnegative r
    rBelowOne : BelowOne r

    QuarticSeriesConverges : Set
    SexticSeriesConverges : Set

    quarticSeriesConverges : QuarticSeriesConverges
    sexticSeriesConverges : SexticSeriesConverges

open PolynomialGeometricSummability public

------------------------------------------------------------------------
-- 8. Frontier.
------------------------------------------------------------------------

record EisensteinCoefficientMajorantBoundary : Set where
  constructor eisenstein-coefficient-majorant-boundary
  field
    sigma3Executable : Bool
    sigma5Executable : Bool
    sigma3QuarticBoundUsed : Bool
    sigma5SexticBoundUsed : Bool
    complexE4TermReducedToQuarticGeometricMajorant : Bool
    complexE6TermReducedToSexticGeometricMajorant : Bool

    selectedComplexNormLawsInstantiated : Bool
    polynomialGeometricSummabilityInstantiated : Bool

    nextResidual : String

open EisensteinCoefficientMajorantBoundary public

canonicalEisensteinCoefficientMajorantBoundary :
  EisensteinCoefficientMajorantBoundary
canonicalEisensteinCoefficientMajorantBoundary =
  eisenstein-coefficient-majorant-boundary
    true true true true true true
    false false
    "instantiate the selected complex norm laws, then prove the pure-real lemma sum n^k r^n converges for k=4,6 and 0<=r<1; all divisor-sum and complex coefficient bookkeeping is already discharged"
