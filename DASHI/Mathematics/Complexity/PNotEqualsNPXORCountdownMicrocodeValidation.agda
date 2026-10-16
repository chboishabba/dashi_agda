module DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: XOR / BIPERMUTATIVE CLOCK MICROCODE
--
-- This validation intentionally imports the production owner.  The ripple
-- countdown names below are required before their implementation is added.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeExact
  using
    ( xorRecoverLeft
    ; xorRecoverRight
    ; sameXorOutputDifferentBorrow
    ; countdownBitFalseBorrow
    ; countdownBitTrueBorrow
    ; countdownBitsNoBorrow
    ; decrementOne
    ; decrementTwo
    ; decrementFour
    ; canonicalXORCountdownBoundary
    )
