module DASHI.Mathematics.Complexity.CodedFiniteStaticBitLookupValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: fixed-description answer stream -> literal stop rules.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.CodedFiniteStaticBitLookupExact
  using
    ( staticLookupExtension
    ; staticLookupFragment
    ; staticLookupCode
    ; stopRuleAtOccurs
    ; stopRuleWritesTableBit
    ; stopRuleTargetsTerminal
    ; canonicalStaticBitLookupBoundary
    )
