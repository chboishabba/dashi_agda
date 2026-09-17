module DASHI.Moonshine.JInvariantEisensteinCalculatorQSubstitutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series
import DASHI.Moonshine.JInvariantConstructedComplexQCalculatorSameExpressionExact as Q

------------------------------------------------------------------------
-- CALCULATOR-q SUBSTITUTION INTO THE EXISTING FINITE EISENSTEIN PRODUCER
--
-- The finite E4/E6 recurrence already uses qOf C tau.  The q calculator seam
-- proves that one actual CalculatorExpr evaluates to exactly that same qOf.
-- Here we replace only the q source in the finite recurrence and prove the
-- resulting E4/E6/discriminant-numerator values are unchanged.
--
-- This is finite executable substitution only.  It creates no infinite-series
-- convergence, modular-form, Klein-j, or RH authority.
------------------------------------------------------------------------

e4TruncatedCalculatorQ :
  (C : Complex.ConstructedComplexPackage) ->
  Series.DivisorPowerKernel ->
  Nat ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
e4TruncatedCalculatorQ C kernel zero tau = Complex.oneC
e4TruncatedCalculatorQ C kernel (suc n) tau =
  Complex._+C_
    (e4TruncatedCalculatorQ C kernel n tau)
    (Series.scaleNatC
      (240 * Series.sigma3 kernel (suc n))
      (Series.powC (Q.evalQOfCalculator C tau) (suc n)))

e6TruncatedCalculatorQ :
  (C : Complex.ConstructedComplexPackage) ->
  Series.DivisorPowerKernel ->
  Nat ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
e6TruncatedCalculatorQ C kernel zero tau = Complex.oneC
e6TruncatedCalculatorQ C kernel (suc n) tau =
  Complex._-C_
    (e6TruncatedCalculatorQ C kernel n tau)
    (Series.scaleNatC
      (504 * Series.sigma5 kernel (suc n))
      (Series.powC (Q.evalQOfCalculator C tau) (suc n)))

discriminantNumeratorCalculatorQ :
  (C : Complex.ConstructedComplexPackage) ->
  Series.DivisorPowerKernel ->
  Nat ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
discriminantNumeratorCalculatorQ C kernel n tau =
  Complex._-C_
    (Series.cubeC (e4TruncatedCalculatorQ C kernel n tau))
    (Series.squareC (e6TruncatedCalculatorQ C kernel n tau))

------------------------------------------------------------------------
-- Exact recurrence preservation.
------------------------------------------------------------------------

e4TruncatedCalculatorQMatches :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  e4TruncatedCalculatorQ C kernel n tau
  ≡ Series.e4Truncated C kernel n tau
e4TruncatedCalculatorQMatches C kernel zero tau = refl
e4TruncatedCalculatorQMatches C kernel (suc n) tau
  rewrite e4TruncatedCalculatorQMatches C kernel n tau
        | Q.evalQOfCalculatorIsQOf C tau = refl

e6TruncatedCalculatorQMatches :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  e6TruncatedCalculatorQ C kernel n tau
  ≡ Series.e6Truncated C kernel n tau
e6TruncatedCalculatorQMatches C kernel zero tau = refl
e6TruncatedCalculatorQMatches C kernel (suc n) tau
  rewrite e6TruncatedCalculatorQMatches C kernel n tau
        | Q.evalQOfCalculatorIsQOf C tau = refl

discriminantNumeratorCalculatorQMatches :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Series.DivisorPowerKernel) ->
  (n : Nat) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  discriminantNumeratorCalculatorQ C kernel n tau
  ≡ Series.discriminantNumeratorTruncated C kernel n tau
discriminantNumeratorCalculatorQMatches C kernel n tau
  rewrite e4TruncatedCalculatorQMatches C kernel n tau
        | e6TruncatedCalculatorQMatches C kernel n tau = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteSubstitutionCreatesInfiniteEisenstein : Set where
data FiniteSubstitutionCreatesKleinJ : Set where
data FiniteSubstitutionCreatesModularity : Set where
data FiniteSubstitutionCreatesRH : Set where

finiteSubstitutionDoesNotCreateInfiniteEisenstein :
  FiniteSubstitutionCreatesInfiniteEisenstein -> ⊥
finiteSubstitutionDoesNotCreateInfiniteEisenstein ()

finiteSubstitutionDoesNotCreateKleinJ : FiniteSubstitutionCreatesKleinJ -> ⊥
finiteSubstitutionDoesNotCreateKleinJ ()

finiteSubstitutionDoesNotCreateModularity : FiniteSubstitutionCreatesModularity -> ⊥
finiteSubstitutionDoesNotCreateModularity ()

finiteSubstitutionDoesNotCreateRH : FiniteSubstitutionCreatesRH -> ⊥
finiteSubstitutionDoesNotCreateRH ()

record EisensteinCalculatorQSubstitutionBoundary : Set where
  constructor eisenstein-calculator-q-substitution-boundary
  field
    theoremBearingFiniteQProducerReused : Bool
    calculatorQSameExpressionReused : Bool
    finiteE4Preserved : Bool
    finiteE6Preserved : Bool
    discriminantNumeratorPreserved : Bool
    infiniteSeriesConvergencePaidHere : Bool
    kleinJPaidHere : Bool
    modularityPaidHere : Bool
    rhPaidHere : Bool
    nextResidual : String
open EisensteinCalculatorQSubstitutionBoundary public

canonicalEisensteinCalculatorQSubstitutionBoundary :
  EisensteinCalculatorQSubstitutionBoundary
canonicalEisensteinCalculatorQSubstitutionBoundary =
  eisenstein-calculator-q-substitution-boundary
    true true true true true
    false false false false
    "reuse these exact finite substitution theorems in the existing constructed Klein-j backend; do not promote finite truncation to the infinite modular forms without the already-separated analytic convergence payment"
