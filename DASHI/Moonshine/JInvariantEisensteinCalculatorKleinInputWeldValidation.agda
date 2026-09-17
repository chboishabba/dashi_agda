module DASHI.Moonshine.JInvariantEisensteinCalculatorKleinInputWeldValidation where

open import DASHI.Core.Prelude

import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series
import DASHI.Moonshine.JInvariantEisensteinConstructedKleinJExact as Klein
import DASHI.Moonshine.JInvariantEisensteinCalculatorKleinInputWeldExact as P

finiteG2Regression :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  P.calculatorG2 C kernel n tau ≡ Series.e4Truncated C kernel n tau
finiteG2Regression = P.calculatorG2Matches

normalizedDeltaRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (normalization : Klein.EisensteinNormalizationData C D F) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  P.calculatorNormalizedDelta C D F kernel n normalization tau
  ≡ P.existingNormalizedDeltaAt C D F kernel n normalization tau
normalizedDeltaRegression = P.calculatorNormalizedDeltaMatches

directNumeratorRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  P.calculatorDirectJNumerator C kernel n tau
  ≡ P.existingDirectJNumerator C kernel n tau
directNumeratorRegression = P.calculatorDirectJNumeratorMatches
