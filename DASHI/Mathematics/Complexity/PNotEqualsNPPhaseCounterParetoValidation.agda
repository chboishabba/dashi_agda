module DASHI.Mathematics.Complexity.PNotEqualsNPPhaseCounterParetoValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: exact phase-lift vs compact XOR-counter accounting.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.PNotEqualsNPPhaseCounterParetoExact
  using
    ( compactCounterStateCountExact
    ; compactCounterRuleCountExact
    ; compactCounterSingleDecrementBound
    ; phaseExpandedStateCountExact
    ; phaseExpandedRuleCountExact
    ; canonicalPhaseCounterParetoBoundary
    )
