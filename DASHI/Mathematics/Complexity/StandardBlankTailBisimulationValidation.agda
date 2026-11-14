module DASHI.Mathematics.Complexity.StandardBlankTailBisimulationValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: implicit vs explicitly materialised blank tails.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.StandardBlankTailBisimulationExact
  using
    ( ListBlankTailEq
    ; ConfigurationBlankTailEq
    ; standardApplyTransitionPreservesBlankTailEq
    ; standardNextPreservesBlankTailEq
    ; transportExactRunAcrossBlankTailEq
    ; blankTailBisimulationBoundary
    )
