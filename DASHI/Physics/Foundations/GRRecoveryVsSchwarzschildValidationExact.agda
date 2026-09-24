{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRRecoveryVsSchwarzschildValidationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.BianchiLovelockCompletion as GR
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.RecoveredGRAttachmentExact as Attach

------------------------------------------------------------------------
-- GENERIC GR RECOVERY != SCHWARZSCHILD KNOWN-LIMIT VALIDATION
--
-- RecoveredGRAttachment is a same-object theorem for an arbitrary literal
-- EinsteinContinuumClosure G.  Its compiler to the selected GR target consumes
-- only the attachment and GRRecoveryReceipt.  No radial valuation or
-- Schwarzschild object occurs in that theorem.
--
-- Schwarzschild/weak-field recovery is still important physical validation,
-- but it is not an irreducible premise of generic same-object GR attachment.
------------------------------------------------------------------------

record GenericRecoveredGRSameObject
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    literalGR :
      GR.EinsteinContinuumClosure

    attachment :
      Attach.RecoveredGRAttachment U literalGR

open GenericRecoveredGRSameObject public

genericRecoveredGRIsSelectedTarget :
  ∀ {U : Weld.UnifiedCandidate} →
  GenericRecoveredGRSameObject U →
  Weld.GRRecoveryReceipt U →
  ∀ candidate regime →
  Weld.grRegime U regime →
  literalGR recovered ≡ Weld.grTarget U (Weld.coarseGrain U candidate regime)
genericRecoveredGRIsSelectedTarget recovered grReceipt =
  Attach.recoveredAttachmentImpliesSelectedGRTarget
    (attachment recovered)
    grReceipt

schwarzschildRadialValuationRequiredForGenericAttachment : Bool
schwarzschildRadialValuationRequiredForGenericAttachment = false

schwarzschildRadialValuationRequiredForGenericAttachmentIsFalse :
  schwarzschildRadialValuationRequiredForGenericAttachment ≡ false
schwarzschildRadialValuationRequiredForGenericAttachmentIsFalse = refl

schwarzschildWeakFieldValidationStillPhysicallyRequired : Bool
schwarzschildWeakFieldValidationStillPhysicallyRequired = true

schwarzschildWeakFieldValidationStillPhysicallyRequiredIsTrue :
  schwarzschildWeakFieldValidationStillPhysicallyRequired ≡ true
schwarzschildWeakFieldValidationStillPhysicallyRequiredIsTrue = refl

genericGRSameObjectStillRequiresLiteralRecoveredAttachment : Bool
genericGRSameObjectStillRequiresLiteralRecoveredAttachment = true

genericGRSameObjectStillRequiresLiteralRecoveredAttachmentIsTrue :
  genericGRSameObjectStillRequiresLiteralRecoveredAttachment ≡ true
genericGRSameObjectStillRequiresLiteralRecoveredAttachmentIsTrue = refl
