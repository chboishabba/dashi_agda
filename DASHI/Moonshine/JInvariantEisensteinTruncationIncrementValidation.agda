module DASHI.Moonshine.JInvariantEisensteinTruncationIncrementValidation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Finite
import DASHI.Moonshine.JInvariantEisensteinTruncationIncrementExact as P

e4SuccessorRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Finite.e4Truncated C kernel (Agda.Builtin.Nat.suc n) tau
  ≡ Complex._+C_
      (Finite.e4Truncated C kernel n tau)
      (P.e4Increment C kernel n tau)
e4SuccessorRegression = P.e4SuccessorIsPreviousPlusIncrement

e6SuccessorRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Finite.e6Truncated C kernel (Agda.Builtin.Nat.suc n) tau
  ≡ Complex._-C_
      (Finite.e6Truncated C kernel n tau)
      (P.e6Increment C kernel n tau)
e6SuccessorRegression = P.e6SuccessorIsPreviousMinusIncrement

e4RealIncrementRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Complex.re (Finite.e4Truncated C kernel (Agda.Builtin.Nat.suc n) tau)
  ≡ Real._+_ (Real.real (Complex.realPackage C))
      (Complex.re (Finite.e4Truncated C kernel n tau))
      (Complex.re (P.e4Increment C kernel n tau))
e4RealIncrementRegression = P.e4RealSuccessorIncrement

e6RealIncrementRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (kernel : Finite.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  (n : Nat) ->
  Complex.re (Finite.e6Truncated C kernel (Agda.Builtin.Nat.suc n) tau)
  ≡ Real._-_ (Real.real (Complex.realPackage C))
      (Complex.re (Finite.e6Truncated C kernel n tau))
      (Complex.re (P.e6Increment C kernel n tau))
e6RealIncrementRegression = P.e6RealSuccessorIncrement
