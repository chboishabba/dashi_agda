module DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCandidateCodeRealizationValidation where

------------------------------------------------------------------------
-- RED-FIRST VALIDATION: bind old candidate-code socket to the actual coded TM.
------------------------------------------------------------------------

open import DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCandidateCodeRealizationExact
  using
    ( SameCandidateCode
    ; sameCandidateCodeProjectionExact
    ; haltingCandidateCodeRealization
    ; haltingCandidateCodeIsLiteralCode
    ; haltingCandidateCodeDecisionFromActualFinish
    ; canonicalHaltingCandidateCodeBoundary
    )
