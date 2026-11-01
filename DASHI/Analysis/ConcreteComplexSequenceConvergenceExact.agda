module DASHI.Analysis.ConcreteComplexSequenceConvergenceExact where

------------------------------------------------------------------------
-- COMPONENTWISE CAUCHY COMPLETENESS FOR ConcreteComplex.ComplexPair
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- `ConstructedOrderedCompleteReal` already carries an actual sequence type,
-- Cauchy predicate, convergence predicate, and cauchyLimit constructor.  The
-- finite Eisenstein recurrence evaluates in `ConcreteComplex.ComplexPair R`.
-- This module lifts the real completeness constructor componentwise to that
-- exact complex carrier; no second complex-number representation or analytic
-- axiom is introduced.
--
-- This is deliberately only a completeness compiler.  A consumer must still
-- prove that the real and imaginary partial-sum sequences of its concrete
-- complex series are Cauchy.
------------------------------------------------------------------------

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (proj₁; proj₂)

import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConstructiveRealSpine as Real

record ComplexSequence (R : Real.ConstructedOrderedCompleteReal) : Set where
  constructor complex-sequence
  field
    realSequence : Real.Sequence R
    imagSequence : Real.Sequence R

open ComplexSequence public

record ComplexIsCauchy
    {R : Real.ConstructedOrderedCompleteReal}
    (sequence : ComplexSequence R) : Set where
  constructor complex-is-cauchy
  field
    realCauchy : Real.IsCauchy R (realSequence sequence)
    imagCauchy : Real.IsCauchy R (imagSequence sequence)

open ComplexIsCauchy public

record ComplexConvergesTo
    {R : Real.ConstructedOrderedCompleteReal}
    (sequence : ComplexSequence R)
    (limit : Complex.ComplexPair R) : Set where
  constructor complex-converges-to
  field
    realConverges :
      Real.ConvergesTo R (realSequence sequence) (Complex.re limit)
    imagConverges :
      Real.ConvergesTo R (imagSequence sequence) (Complex.im limit)

open ComplexConvergesTo public

complexCauchyLimit :
  ∀ {R : Real.ConstructedOrderedCompleteReal} ->
  (sequence : ComplexSequence R) ->
  ComplexIsCauchy sequence ->
  Σ (Complex.ComplexPair R) (ComplexConvergesTo sequence)
complexCauchyLimit {R} sequence cauchy =
  let
    realLimit =
      Real.cauchyLimit R
        (realSequence sequence)
        (realCauchy cauchy)
    imagLimit =
      Real.cauchyLimit R
        (imagSequence sequence)
        (imagCauchy cauchy)
  in
  Complex.complex (proj₁ realLimit) (proj₁ imagLimit)
  , complex-converges-to (proj₂ realLimit) (proj₂ imagLimit)
