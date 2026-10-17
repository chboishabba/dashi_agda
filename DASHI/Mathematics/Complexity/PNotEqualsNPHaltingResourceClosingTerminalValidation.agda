module DASHI.Mathematics.Complexity.PNotEqualsNPHaltingResourceClosingTerminalValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: actual-halting candidate -> terminal resource compiler.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.PNotEqualsNPHaltingResourceClosingTerminalExact
  using
    ( haltingResourceCompilationGivesDecisionFailure
    ; haltingResourceCompilationGivesPNotEqualsNP
    ; canonicalHaltingResourceTerminalBoundary
    )
