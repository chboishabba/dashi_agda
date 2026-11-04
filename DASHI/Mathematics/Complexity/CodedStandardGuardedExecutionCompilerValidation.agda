module DASHI.Mathematics.Complexity.CodedStandardGuardedExecutionCompilerValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: actual-halting run -> guarded Cook representation.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.GuardedStandardStartBlankTailExact
  using
    ( canonicalProjectionOfInterior
    ; guardedStandardStartBlankTailEq
    ; canonicalGuardedStartBlankTailBoundary
    )

open import DASHI.Mathematics.Complexity.CodedStandardGuardedExecutionCompilerExact
  using
    ( guardedExecutionReceiptOfHaltingWitness
    ; canonicalGuardedExecutionCompilerBoundary
    )
