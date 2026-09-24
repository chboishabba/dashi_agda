module DASHI.Analysis.ConcreteComplexSequenceConvergenceValidation where

open import Agda.Builtin.Sigma using (Σ)

import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplexSequenceConvergenceExact as P

componentwiseCauchyLimitCompiler :
  ∀ {R : Real.ConstructedOrderedCompleteReal} ->
  (sequence : P.ComplexSequence R) ->
  P.ComplexIsCauchy sequence ->
  Σ (Complex.ComplexPair R) (P.ComplexConvergesTo sequence)
componentwiseCauchyLimitCompiler = P.complexCauchyLimit
