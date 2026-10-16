module DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownRuleFragmentValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: literal finite rule-table countdown fragment.
--
-- The downstream imports deliberately turn this into the focused rollup for
-- the compact XOR/ripple timer path:
--
--   local XOR/borrow semantics
--     -> literal three-rule fragment
--     -> width+1 exact work bound
--     -> arbitrary-word StandardExactRun + quiescent endpoint.
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

import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownCostValidation
import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownExactRunValidation
