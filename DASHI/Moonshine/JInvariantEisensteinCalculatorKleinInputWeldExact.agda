module DASHI.Moonshine.JInvariantEisensteinCalculatorKleinInputWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantConstructedComplexKleinJBackendExact as CKlein
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series
import DASHI.Moonshine.JInvariantEisensteinConstructedKleinJExact as Klein
import DASHI.Moonshine.JInvariantEisensteinCalculatorQSubstitutionExact as CalcQ

------------------------------------------------------------------------
-- CALCULATOR-q -> FINITE KLEIN INPUT WELD
--
-- The proof-relevant Klein backend consumes g2 and Delta.  The existing finite
-- Eisenstein owner instantiates these as E4_N and
--
--   Delta_N = (E4_N^3 - E6_N^2) / 1728.
--
-- The calculator-q substitution already proves exact equality of E4_N, E6_N,
-- and the discriminant numerator.  This owner pushes those equalities exactly
-- to the pointwise inputs of the existing Klein construction without claiming
-- equality of proof-relevant quotient evaluators under different nonzero
-- witnesses.
------------------------------------------------------------------------

private
  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) -> Set
  ComplexCarrier C =
    Complex.ComplexPair (Real.real (Complex.realPackage C))

calculatorG2 :
  (C : Complex.ConstructedComplexPackage) ->
  Series.DivisorPowerKernel -> Nat -> ComplexCarrier C -> ComplexCarrier C
calculatorG2 C kernel n tau =
  CalcQ.e4TruncatedCalculatorQ C kernel n tau

calculatorG2Matches :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : ComplexCarrier C) ->
  calculatorG2 C kernel n tau ≡ Series.e4Truncated C kernel n tau
calculatorG2Matches = CalcQ.e4TruncatedCalculatorQMatches

existingNormalizedDeltaAt :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  Klein.EisensteinNormalizationData C D F ->
  ComplexCarrier C -> ComplexCarrier C
existingNormalizedDeltaAt C D F kernel n normalization tau =
  CKlein.quotientC F
    (Series.discriminantNumeratorTruncated C kernel n tau)
    (Klein.scalar1728 C)
    (Klein.scalar1728Nonzero normalization)

calculatorNormalizedDelta :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  Klein.EisensteinNormalizationData C D F ->
  ComplexCarrier C -> ComplexCarrier C
calculatorNormalizedDelta C D F kernel n normalization tau =
  CKlein.quotientC F
    (CalcQ.discriminantNumeratorCalculatorQ C kernel n tau)
    (Klein.scalar1728 C)
    (Klein.scalar1728Nonzero normalization)

calculatorNormalizedDeltaMatches :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (normalization : Klein.EisensteinNormalizationData C D F) ->
  (tau : ComplexCarrier C) ->
  calculatorNormalizedDelta C D F kernel n normalization tau
  ≡ existingNormalizedDeltaAt C D F kernel n normalization tau
calculatorNormalizedDeltaMatches C D F kernel n normalization tau
  rewrite CalcQ.discriminantNumeratorCalculatorQMatches C kernel n tau = refl

existingDirectJNumerator :
  (C : Complex.ConstructedComplexPackage) ->
  Series.DivisorPowerKernel -> Nat -> ComplexCarrier C -> ComplexCarrier C
existingDirectJNumerator C kernel n tau =
  Series.scaleNatC 1728
    (Series.cubeC (Series.e4Truncated C kernel n tau))

calculatorDirectJNumerator :
  (C : Complex.ConstructedComplexPackage) ->
  Series.DivisorPowerKernel -> Nat -> ComplexCarrier C -> ComplexCarrier C
calculatorDirectJNumerator C kernel n tau =
  Series.scaleNatC 1728
    (Series.cubeC (CalcQ.e4TruncatedCalculatorQ C kernel n tau))

calculatorDirectJNumeratorMatches :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : ComplexCarrier C) ->
  calculatorDirectJNumerator C kernel n tau
  ≡ existingDirectJNumerator C kernel n tau
calculatorDirectJNumeratorMatches C kernel n tau
  rewrite CalcQ.e4TruncatedCalculatorQMatches C kernel n tau = refl

------------------------------------------------------------------------
-- Why the final proof-relevant quotient is intentionally not equated here.
------------------------------------------------------------------------

data InputEqualityCreatesNonzeroWitnessEquality : Set where
data InputEqualityCreatesProofRelevantQuotientEquality : Set where
data FiniteKleinInputWeldCreatesAnalyticJ : Set where
data FiniteKleinInputWeldCreatesRH : Set where

inputEqualityDoesNotCreateNonzeroWitnessEquality :
  InputEqualityCreatesNonzeroWitnessEquality -> ⊥
inputEqualityDoesNotCreateNonzeroWitnessEquality ()

inputEqualityDoesNotCreateProofRelevantQuotientEquality :
  InputEqualityCreatesProofRelevantQuotientEquality -> ⊥
inputEqualityDoesNotCreateProofRelevantQuotientEquality ()

finiteKleinInputWeldDoesNotCreateAnalyticJ :
  FiniteKleinInputWeldCreatesAnalyticJ -> ⊥
finiteKleinInputWeldDoesNotCreateAnalyticJ ()

finiteKleinInputWeldDoesNotCreateRH : FiniteKleinInputWeldCreatesRH -> ⊥
finiteKleinInputWeldDoesNotCreateRH ()

record EisensteinCalculatorKleinInputBoundary : Set where
  constructor eisenstein-calculator-klein-input-boundary
  field
    finiteKleinOwnerReused : Bool
    calculatorQSubstitutionReused : Bool
    g2InputEqualityPaid : Bool
    normalizedDeltaInputEqualityPaid : Bool
    directNumeratorEqualityPaid : Bool
    proofRelevantQuotientEqualityPaid : Bool
    finiteEqualsAnalyticJPaid : Bool
    rhPaid : Bool
    nextResidual : String
open EisensteinCalculatorKleinInputBoundary public

canonicalEisensteinCalculatorKleinInputBoundary :
  EisensteinCalculatorKleinInputBoundary
canonicalEisensteinCalculatorKleinInputBoundary =
  eisenstein-calculator-klein-input-boundary
    true true true true true
    false false false
    "either reuse an existing theorem that quotientC is independent of the chosen NonzeroC witness or explicitly transport one certified point/witness through the calculator-q input equalities; do not collapse proof-relevant quotient data by definitional equality"
