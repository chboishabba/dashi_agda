module DASHI.Moonshine.JInvariantEisensteinCalculatorKleinInputWeldValidation where

open import DASHI.Core.Prelude

import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantConstructedComplexKleinJBackendExact as CKlein
import DASHI.Moonshine.JInvariantProofRelevantKleinJExact as ProofKlein
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series
import DASHI.Moonshine.JInvariantEisensteinInternalDivisorPowerKernelExact as Internal
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

quotientWitnessRegression :
  ∀ {R : Real.ConstructedOrderedCompleteReal}
    {D : Polar.RealDivisionAndSquareRoot R} ->
  (F : Polar.ComplexFieldAuthority R D) ->
  (numerator denominator : Complex.ComplexPair R) ->
  (nz₁ nz₂ : Polar.NonzeroC F denominator) ->
  CKlein.quotientC F numerator denominator nz₁
  ≡ CKlein.quotientC F numerator denominator nz₂
quotientWitnessRegression = P.quotientCWitnessIndependent

directJRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (normalization : Klein.EisensteinNormalizationData C D F) ->
  (point : Klein.CertifiedFiniteEisensteinPoint C D F kernel n normalization) ->
  P.directJTruncatedCalculatorQ C D F kernel n normalization point
  ≡ Klein.directJTruncated C D F kernel n normalization point
directJRegression = P.directJTruncatedCalculatorQMatches

sourceFacingKleinRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (normalization : Klein.EisensteinNormalizationData C D F) ->
  (agreement : Klein.EisensteinKleinNormalizationAgreement C D F kernel n normalization) ->
  (point : Klein.CertifiedFiniteEisensteinPoint C D F kernel n normalization) ->
  ProofKlein.KleinJ (Klein.eisensteinKlein C D F kernel n normalization) point
  ≡ P.directJTruncatedCalculatorQ C D F kernel n normalization point
sourceFacingKleinRegression = P.sourceFacingKleinJCalculatorQMatches

internalDirectJRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (n : Nat) ->
  (normalization : Klein.EisensteinNormalizationData C D F) ->
  (point : Klein.CertifiedFiniteEisensteinPoint C D F Internal.internalDivisorPowerKernel n normalization) ->
  P.directJTruncatedInternalCalculatorQ C D F n normalization point
  ≡ Klein.directJTruncated C D F Internal.internalDivisorPowerKernel n normalization point
internalDirectJRegression = P.directJTruncatedInternalCalculatorQMatches

internalSourceFacingKleinRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (n : Nat) ->
  (normalization : Klein.EisensteinNormalizationData C D F) ->
  (agreement : Klein.EisensteinKleinNormalizationAgreement C D F Internal.internalDivisorPowerKernel n normalization) ->
  (point : Klein.CertifiedFiniteEisensteinPoint C D F Internal.internalDivisorPowerKernel n normalization) ->
  ProofKlein.KleinJ
    (Klein.eisensteinKlein C D F Internal.internalDivisorPowerKernel n normalization)
    point
  ≡ P.directJTruncatedInternalCalculatorQ C D F n normalization point
internalSourceFacingKleinRegression = P.sourceFacingKleinJInternalCalculatorQMatches
