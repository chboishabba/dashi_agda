module DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityClosureValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: canonical deterministic unary-field equality closure.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityDeterminismExact
  using (dispatchUnique; equalityCode)

open import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityClosureExact
  using
    ( fieldEqualityDispatchUnique
    ; fieldEqualityCode
    ; fieldEqualityMachine
    ; equalSinkQuiescent
    ; unequalSinkQuiescent
    )
