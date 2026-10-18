module DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitCompilerValidation where

open import Agda.Builtin.Sigma using (Σ)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Convergence
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConcreteComplexSequenceConvergenceExact as ComplexConvergence
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Eisenstein
import DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitCompilerExact as P

------------------------------------------------------------------------
-- RED owner for the exact finite-truncation -> same-carrier limit compiler.
--
-- This deliberately asks only for a compiler from explicit componentwise
-- Cauchy evidence.  It must not manufacture the still-unpaid quantitative
-- Cauchy estimate or identify the resulting limit with the analytic lattice
-- Eisenstein sum.
------------------------------------------------------------------------

e4SameCarrierLimitCompiler :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Convergence.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Eisenstein.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  ComplexConvergence.ComplexIsCauchy
    (P.e4TruncationSequence C S kernel tau) ->
  Σ (Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (ComplexConvergence.ComplexConvergesTo
      (P.e4TruncationSequence C S kernel tau))
e4SameCarrierLimitCompiler = P.e4TruncationLimit

e6SameCarrierLimitCompiler :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Convergence.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Eisenstein.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  ComplexConvergence.ComplexIsCauchy
    (P.e6TruncationSequence C S kernel tau) ->
  Σ (Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (ComplexConvergence.ComplexConvergesTo
      (P.e6TruncationSequence C S kernel tau))
e6SameCarrierLimitCompiler = P.e6TruncationLimit
