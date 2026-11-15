module DASHI.Mathematics.Complexity.GuardedCookStaticBitTableValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: SAME guarded-Cook formula -> literal static bit table.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.GuardedCookStaticBitTableExact
  using
    ( formulaBitsShape
    ; formulaTable
    ; formulaStaticLookupCode
    ; formulaTableLookupExact
    ; descriptionQueryAnswerAtFiniteIndexExact
    ; canonicalGuardedCookStaticBitTableBoundary
    )
