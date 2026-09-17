module DASHI.Moonshine.JInvariantEisensteinCalculatorQSubstitutionValidation where

open import DASHI.Core.Prelude

import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series
import DASHI.Moonshine.JInvariantEisensteinCalculatorQSubstitutionExact as P

finiteE4Regression :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  P.e4TruncatedCalculatorQ C kernel n tau
  ≡ Series.e4Truncated C kernel n tau
finiteE4Regression = P.e4TruncatedCalculatorQMatches

finiteE6Regression :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  P.e6TruncatedCalculatorQ C kernel n tau
  ≡ Series.e6Truncated C kernel n tau
finiteE6Regression = P.e6TruncatedCalculatorQMatches

discriminantRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  P.discriminantNumeratorCalculatorQ C kernel n tau
  ≡ Series.discriminantNumeratorTruncated C kernel n tau
discriminantRegression = P.discriminantNumeratorCalculatorQMatches
