module DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseSizeValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: quantify the program-size cost of exact phase lifting.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseSizeExact
  using
    ( allFinLengthExact
    ; phaseLiftRuleCountExact
    ; phaseLiftStateCountExact
    ; canonicalPhaseLiftSizeBoundary
    )
