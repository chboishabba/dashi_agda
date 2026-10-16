module DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: XOR / BIPERMUTATIVE CLOCK MICROCODE
--
-- This validation intentionally imports the production owner.  It was added
-- first so the source dependency is explicit before implementation.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeExact
  using
    ( xorRecoverLeft
    ; xorRecoverRight
    ; sameXorOutputDifferentBorrow
    ; countdownBitFalseBorrow
    ; countdownBitTrueBorrow
    ; canonicalXORCountdownBoundary
    )
