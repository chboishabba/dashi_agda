module DASHI.Moonshine.JInvariantEisensteinInternalDivisorPowerKernelValidation where

open import DASHI.Core.Prelude

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series
import DASHI.Moonshine.JInvariantEisensteinInternalDivisorPowerKernelExact as P

sigma3KernelRegression :
  (n : Nat) ->
  Series.sigma3 P.internalDivisorPowerKernel n ≡ Divisor.sigma3 n
sigma3KernelRegression n = refl

sigma5KernelRegression :
  (n : Nat) ->
  Series.sigma5 P.internalDivisorPowerKernel n ≡ Divisor.sigma5 n
sigma5KernelRegression n = refl

e4ZeroRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  P.e4Internal C zero tau ≡ Complex.oneC
e4ZeroRegression C tau = refl

e6ZeroRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  P.e6Internal C zero tau ≡ Complex.oneC
e6ZeroRegression C tau = refl

kernelExternalDebtPaid :
  P.divisorPowerKernelExternalOnInternalRoute
    P.canonicalInternalEisensteinKernelBoundary
  ≡ false
kernelExternalDebtPaid = refl

finiteEqualsInfiniteStillFalse :
  P.finiteEqualsInfiniteAnalyticEisenstein
    P.canonicalInternalEisensteinKernelBoundary
  ≡ false
finiteEqualsInfiniteStillFalse = refl
