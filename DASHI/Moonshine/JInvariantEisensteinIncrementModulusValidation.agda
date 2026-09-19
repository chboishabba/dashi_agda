module DASHI.Moonshine.JInvariantEisensteinIncrementModulusValidation where

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Series
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Finite
import DASHI.Moonshine.JInvariantEisensteinInternalDivisorPowerKernelExact as Internal
import DASHI.Moonshine.JInvariantEisensteinTruncationIncrementExact as Increment
import DASHI.Moonshine.JInvariantQPowerModulusExact as QPower
import DASHI.Moonshine.JInvariantEisensteinIncrementModulusExact as P

e4IncrementModulusRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} →
  (M : QPower.ComplexModulusMultiplicationLaws C D F) →
  (T : P.ComplexModulusTriangleOrderLaws C D F) →
  (kernel : Finite.DivisorPowerKernel) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  (n : Nat) →
  Real._≤_ (Real.real (Complex.realPackage C))
    (Polar.modulus F (Increment.e4Increment C kernel n tau))
    (P.scaleNatR
      (Real.real (Complex.realPackage C))
      (240 * Finite.sigma3 kernel (suc n))
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus F (Finite.qOf C tau))
        (suc n)))
e4IncrementModulusRegression = P.e4IncrementModulusBound

e6IncrementModulusRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} →
  (M : QPower.ComplexModulusMultiplicationLaws C D F) →
  (T : P.ComplexModulusTriangleOrderLaws C D F) →
  (kernel : Finite.DivisorPowerKernel) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  (n : Nat) →
  Real._≤_ (Real.real (Complex.realPackage C))
    (Polar.modulus F (Increment.e6Increment C kernel n tau))
    (P.scaleNatR
      (Real.real (Complex.realPackage C))
      (504 * Finite.sigma5 kernel (suc n))
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus F (Finite.qOf C tau))
        (suc n)))
e6IncrementModulusRegression = P.e6IncrementModulusBound


e4PolynomialGeometricRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} →
  (M : QPower.ComplexModulusMultiplicationLaws C D F) →
  (T : P.ComplexModulusTriangleOrderLaws C D F) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  (n : Nat) →
  Real._≤_ (Real.real (Complex.realPackage C))
    (Polar.modulus F
      (Increment.e4Increment C Internal.internalDivisorPowerKernel n tau))
    (P.scaleNatR
      (Real.real (Complex.realPackage C))
      (240 * (Divisor.powNat (suc n) 3 * suc n))
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus F (Finite.qOf C tau))
        (suc n)))
e4PolynomialGeometricRegression =
  P.e4InternalPolynomialGeometricModulusBound

e6PolynomialGeometricRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} →
  (M : QPower.ComplexModulusMultiplicationLaws C D F) →
  (T : P.ComplexModulusTriangleOrderLaws C D F) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  (n : Nat) →
  Real._≤_ (Real.real (Complex.realPackage C))
    (Polar.modulus F
      (Increment.e6Increment C Internal.internalDivisorPowerKernel n tau))
    (P.scaleNatR
      (Real.real (Complex.realPackage C))
      (504 * (Divisor.powNat (suc n) 5 * suc n))
      (Series.powerR
        (Real.real (Complex.realPackage C))
        (Polar.modulus F (Finite.qOf C tau))
        (suc n)))
e6PolynomialGeometricRegression =
  P.e6InternalPolynomialGeometricModulusBound
