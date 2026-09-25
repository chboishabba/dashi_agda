{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityBetaTraceBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- BETA / F^2 TRACE BRIDGE
--
-- The repository already owns source-facing running-coupling and vacuum-
-- polarisation coordinates.  Those coordinates do NOT automatically become
-- the CMP119 stress trace.
--
-- This file states the minimum exact bridge needed by the antigravity lane.
-- If the selected weighted quantum trace numerator is identified on the same
-- finite measure with
--
--     betaTraceCoefficient * fieldStrengthSquareNumerator
--
-- and the coefficient is negative while the weighted F^2 numerator is
-- positive, the selected quantum trace numerator is negative.
--
-- All convention-sensitive physics is explicit in the attachment.  In
-- particular, a one-loop beta coefficient alone cannot inhabit this record.
------------------------------------------------------------------------

record BetaTraceNumeratorAttachment
    (selectedQuantumTraceNumerator : ℚ) : Set where
  field
    betaTraceCoefficient : ℚ
    fieldStrengthSquareNumerator : ℚ

    selectedQuantumTraceIsBetaF2 :
      selectedQuantumTraceNumerator
      ≡ betaTraceCoefficient * fieldStrengthSquareNumerator

    betaTraceCoefficientNegative :
      betaTraceCoefficient < 0ℚ

    fieldStrengthSquareNumeratorPositive :
      0ℚ < fieldStrengthSquareNumerator

open BetaTraceNumeratorAttachment public

betaF2ProductNegative :
  ∀ {selectedQuantumTraceNumerator}
    (attachment :
      BetaTraceNumeratorAttachment selectedQuantumTraceNumerator) →
  betaTraceCoefficient attachment
    * fieldStrengthSquareNumerator attachment
  < 0ℚ
betaF2ProductNegative attachment =
  ℚP.*-negative
    (betaTraceCoefficientNegative attachment)
    (fieldStrengthSquareNumeratorPositive attachment)

betaTraceAttachmentGivesQuantumTraceNegative :
  ∀ {selectedQuantumTraceNumerator}
    (attachment :
      BetaTraceNumeratorAttachment selectedQuantumTraceNumerator) →
  selectedQuantumTraceNumerator < 0ℚ
betaTraceAttachmentGivesQuantumTraceNegative
    {selectedQuantumTraceNumerator = selectedQuantumTraceNumerator}
    attachment =
  subst
    (λ value → value < 0ℚ)
    (sym (selectedQuantumTraceIsBetaF2 attachment))
    (betaF2ProductNegative attachment)

oneLoopBetaCoefficientAloneClosesTraceSign : Bool
oneLoopBetaCoefficientAloneClosesTraceSign = false

oneLoopBetaCoefficientAloneClosesTraceSignIsFalse :
  oneLoopBetaCoefficientAloneClosesTraceSign ≡ false
oneLoopBetaCoefficientAloneClosesTraceSignIsFalse = refl

betaF2SameObjectNumeratorAttachmentRequired : Bool
betaF2SameObjectNumeratorAttachmentRequired = true

betaF2SameObjectNumeratorAttachmentRequiredIsTrue :
  betaF2SameObjectNumeratorAttachmentRequired ≡ true
betaF2SameObjectNumeratorAttachmentRequiredIsTrue = refl
