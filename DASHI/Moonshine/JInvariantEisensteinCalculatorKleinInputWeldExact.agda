module DASHI.Moonshine.JInvariantEisensteinCalculatorKleinInputWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Analysis.OrdinaryComplexInverseWitnessIndependenceExact as Inverse
import DASHI.Moonshine.JInvariantConstructedComplexKleinJBackendExact as CKlein
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series
import DASHI.Moonshine.JInvariantEisensteinConstructedKleinJExact as Klein
import DASHI.Moonshine.JInvariantEisensteinCalculatorQSubstitutionExact as CalcQ

------------------------------------------------------------------------
-- CALCULATOR-q -> FINITE KLEIN WELD
--
-- The proof-relevant Klein backend consumes g2 and Delta.  The existing finite
-- Eisenstein owner instantiates these as E4_N and
--
--   Delta_N = (E4_N^3 - E6_N^2) / 1728.
--
-- The calculator-q substitution proves exact equality of E4_N, E6_N, and the
-- discriminant numerator.  We first push those equalities to the Klein inputs.
-- Then we use the generic uniqueness of the existing reciprocal/inverse value
-- to remove dependence on which NonzeroC proof was transported, allowing the
-- direct finite Klein-j evaluator itself to be welded exactly.
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
-- Generic quotient value does not depend on the proof of nonzeroness.
------------------------------------------------------------------------

quotientCWitnessIndependent :
  ∀ {R : Real.ConstructedOrderedCompleteReal}
    {D : Polar.RealDivisionAndSquareRoot R} ->
  (F : Polar.ComplexFieldAuthority R D) ->
  (numerator denominator : Complex.ComplexPair R) ->
  (nz₁ nz₂ : Polar.NonzeroC F denominator) ->
  CKlein.quotientC F numerator denominator nz₁
  ≡ CKlein.quotientC F numerator denominator nz₂
quotientCWitnessIndependent F numerator denominator nz₁ nz₂ =
  cong
    (λ inv -> Complex._*C_ numerator inv)
    (Inverse.complexInverseWitnessIndependent F denominator nz₁ nz₂)

------------------------------------------------------------------------
-- Transport the original certified nonzero denominator to calculator-q form.
------------------------------------------------------------------------

calculatorDiscriminantNonzero :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (normalization : Klein.EisensteinNormalizationData C D F) ->
  (point : Klein.CertifiedFiniteEisensteinPoint C D F kernel n normalization) ->
  Polar.NonzeroC F
    (CalcQ.discriminantNumeratorCalculatorQ C kernel n (Klein.tau point))
calculatorDiscriminantNonzero C D F kernel n normalization point =
  subst
    (Polar.NonzeroC F)
    (sym (CalcQ.discriminantNumeratorCalculatorQMatches
      C kernel n (Klein.tau point)))
    (Klein.discriminantNumeratorNonzero point)

------------------------------------------------------------------------
-- Exact direct finite-j evaluator with calculator q substituted.
------------------------------------------------------------------------

directJTruncatedCalculatorQ :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (normalization : Klein.EisensteinNormalizationData C D F) ->
  Klein.CertifiedFiniteEisensteinPoint C D F kernel n normalization ->
  ComplexCarrier C
directJTruncatedCalculatorQ C D F kernel n normalization point =
  Series.scaleNatC 1728
    (CKlein.quotientC F
      (Series.cubeC
        (CalcQ.e4TruncatedCalculatorQ C kernel n (Klein.tau point)))
      (CalcQ.discriminantNumeratorCalculatorQ C kernel n (Klein.tau point))
      (calculatorDiscriminantNonzero C D F kernel n normalization point))

directJTruncatedCalculatorQMatches :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority (Real.real (Complex.realPackage C)) D) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (normalization : Klein.EisensteinNormalizationData C D F) ->
  (point : Klein.CertifiedFiniteEisensteinPoint C D F kernel n normalization) ->
  directJTruncatedCalculatorQ C D F kernel n normalization point
  ≡ Klein.directJTruncated C D F kernel n normalization point
directJTruncatedCalculatorQMatches C D F kernel n normalization point
  rewrite CalcQ.e4TruncatedCalculatorQMatches C kernel n (Klein.tau point)
        | CalcQ.discriminantNumeratorCalculatorQMatches C kernel n (Klein.tau point) =
  cong
    (Series.scaleNatC 1728)
    (quotientCWitnessIndependent F
      (Series.cubeC (Series.e4Truncated C kernel n (Klein.tau point)))
      (Series.discriminantNumeratorTruncated C kernel n (Klein.tau point))
      (calculatorDiscriminantNonzero C D F kernel n normalization point)
      (Klein.discriminantNumeratorNonzero point))

------------------------------------------------------------------------
-- Remaining authority firewalls.
------------------------------------------------------------------------

data FiniteKleinEqualityCreatesAnalyticJ : Set where
data FiniteKleinEqualityCreatesInfiniteSeriesConvergence : Set where
data FiniteKleinEqualityCreatesRH : Set where

finiteKleinEqualityDoesNotCreateAnalyticJ :
  FiniteKleinEqualityCreatesAnalyticJ -> ⊥
finiteKleinEqualityDoesNotCreateAnalyticJ ()

finiteKleinEqualityDoesNotCreateInfiniteSeriesConvergence :
  FiniteKleinEqualityCreatesInfiniteSeriesConvergence -> ⊥
finiteKleinEqualityDoesNotCreateInfiniteSeriesConvergence ()

finiteKleinEqualityDoesNotCreateRH : FiniteKleinEqualityCreatesRH -> ⊥
finiteKleinEqualityDoesNotCreateRH ()

record EisensteinCalculatorKleinInputBoundary : Set where
  constructor eisenstein-calculator-klein-input-boundary
  field
    finiteKleinOwnerReused : Bool
    calculatorQSubstitutionReused : Bool
    g2InputEqualityPaid : Bool
    normalizedDeltaInputEqualityPaid : Bool
    directNumeratorEqualityPaid : Bool
    inverseWitnessIndependencePaid : Bool
    proofRelevantQuotientEqualityPaid : Bool
    directFiniteJEvaluatorEqualityPaid : Bool
    finiteEqualsAnalyticJPaid : Bool
    rhPaid : Bool
    nextResidual : String
open EisensteinCalculatorKleinInputBoundary public

canonicalEisensteinCalculatorKleinInputBoundary :
  EisensteinCalculatorKleinInputBoundary
canonicalEisensteinCalculatorKleinInputBoundary =
  eisenstein-calculator-klein-input-boundary
    true true true true true true true true
    false false
    "the calculator q source is now extensionally invisible to the certified finite direct-j evaluator; the remaining boundary is finite truncation -> infinite analytic modular forms/Klein-j, not proof-witness bookkeeping"
