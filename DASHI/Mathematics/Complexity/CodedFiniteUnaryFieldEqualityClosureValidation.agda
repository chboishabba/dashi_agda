module DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityClosureValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: close unary-field equality microcode into coded TM.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityClosureExact
  using
    ( fieldEqualityKeyUnique
    ; fieldEqualityDispatchUnique
    ; fieldEqualityCode
    ; fieldEqualityMachine
    ; equalSinkQuiescent
    ; unequalSinkQuiescent
    )
