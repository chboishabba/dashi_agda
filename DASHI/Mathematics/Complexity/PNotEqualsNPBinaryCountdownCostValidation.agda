module DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownCostValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: exact XOR/ripple countdown work accounting.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownCostExact
  using
    ( countdownWork
    ; countdownWorkBound
    ; decrementOneWork
    ; decrementTwoWork
    ; decrementFourWork
    ; canonicalBinaryCountdownCostBoundary
    )
