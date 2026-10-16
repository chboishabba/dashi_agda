module DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownExactRunValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: literal arbitrary-word countdown run.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownExactRunExact
  using
    ( countdownCode
    ; countdownMachine
    ; countdownStepEnd
    ; countdownStepFalse
    ; countdownStepTrue
    ; countdownExactRun
    ; countdownFinishQuiescent
    ; canonicalBinaryCountdownExactRunBoundary
    )
