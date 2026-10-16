module DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterFidelityValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: raw self-delimiting interpreter fidelity on actual code.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterFidelityExact
  using
    ( finEqualToNatEqual
    ; rawRuleKeyMatchExact
    ; scanRawRulesExact
    ; fetchRawActualExact
    ; rawApplyRuleExact
    ; rawNextExact
    ; rawIterateFollowsStandardRun
    ; selfDelimitedInterpreterFollowsStandardRun
    )
