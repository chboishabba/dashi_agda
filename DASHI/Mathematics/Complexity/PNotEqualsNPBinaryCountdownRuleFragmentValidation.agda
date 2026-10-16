module DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownRuleFragmentValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: literal finite rule-table countdown fragment.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownRuleFragmentExact
  using
    ( countdownFragment
    ; borrowOnZeroRule
    ; resolveOnOneRule
    ; underflowOnEndRule
    ; resolvedControlHasNoResidentRule
    ; underflowControlHasNoResidentRule
    )
