module DASHI.Mathematics.Complexity.CodedStandardGuardedExecutionCompilerValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: actual-halting run -> guarded Cook representation.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.CodedStandardGuardedExecutionCompilerExact
  using
    ( canonicalProjectionOfInterior
    ; guardedStandardStartBlankTailEq
    ; guardedExecutionReceiptOfHaltingWitness
    ; canonicalGuardedExecutionCompilerBoundary
    )
