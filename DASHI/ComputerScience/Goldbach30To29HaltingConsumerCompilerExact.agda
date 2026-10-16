module DASHI.ComputerScience.Goldbach30To29HaltingConsumerCompilerExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.Goldbach29ExternalHaltingSemanticsExact as External29

------------------------------------------------------------------------
-- HALTING-CONSUMER COMPILER
--
-- The final semantic comparison does not require literal state identity or a
-- fine-state bisimulation if both machines are independently proved to realize
-- the SAME declared counterexample consumer.  This module pays that logical
-- compiler exactly and leaves the missing Goldbach30 attachment explicit.
--
-- `Set` is used propositionally here: an inhabitant is evidence of the
-- proposition.  No external Lean theorem is silently coerced into such an Agda
-- inhabitant; the Goldbach29 source receipt remains cross-prover authority only.
------------------------------------------------------------------------

record LogicalIff (A B : Set) : Set where
  constructor logicalIff
  field
    forward : A → B
    backward : B → A

open LogicalIff public

record HaltingConsumerAttachment
    (Halts Counterexample : Set) : Set where
  constructor haltingConsumerAttachment
  field
    haltsIffCounterexample : LogicalIff Halts Counterexample

open HaltingConsumerAttachment public

sameCounterexampleConsumerImpliesHaltingEquivalence :
  ∀ {Halts30 Halts29 Counterexample : Set} →
  HaltingConsumerAttachment Halts30 Counterexample →
  HaltingConsumerAttachment Halts29 Counterexample →
  LogicalIff Halts30 Halts29
sameCounterexampleConsumerImpliesHaltingEquivalence left right =
  logicalIff
    (λ h30 →
      backward (haltsIffCounterexample right)
        (forward (haltsIffCounterexample left) h30))
    (λ h29 →
      backward (haltsIffCounterexample left)
        (forward (haltsIffCounterexample right) h29))

haltingEquivalencePreservesCounterexampleConsumer :
  ∀ {Halts30 Halts29 Counterexample : Set}
    (left : HaltingConsumerAttachment Halts30 Counterexample)
    (right : HaltingConsumerAttachment Halts29 Counterexample)
    (h30 : Halts30) →
  Counterexample
haltingEquivalencePreservesCounterexampleConsumer left right h30 =
  forward (haltsIffCounterexample left) h30

------------------------------------------------------------------------
-- Source-status cut.
------------------------------------------------------------------------

goldbach29ExternalSourceCanFillRightHandRole : Bool
goldbach29ExternalSourceCanFillRightHandRole =
  External29.externalGoldbach29HaltingSemanticsSourcePaid

-- No Agda inhabitant of HaltingConsumerAttachment is manufactured from the
-- Lean source receipt.  A source-native/cross-prover adapter could supply it;
-- alternatively a Goldbach30 theorem against the same counterexample consumer
-- plus an accepted cross-prover transport closes the semantic comparison.

goldbach30HaltingAttachmentPaid : Bool
goldbach30HaltingAttachmentPaid = false

goldbach29AgdaHaltingAttachmentPaid : Bool
goldbach29AgdaHaltingAttachmentPaid = false

record GoldbachHaltingCompilerBoundary : Set where
  constructor goldbachHaltingCompilerBoundary
  field
    sameConsumerCompilerPaid : Bool
    goldbach29ExternalSourceAvailable : Bool
    goldbach29AgdaAttachmentAvailable : Bool
    goldbach30AttachmentAvailable : Bool
    literalFineStateIdentityRequiredForHaltingEquivalence : Bool
    fullWeakBisimulationRequiredIfSameConsumerAttachmentsExist : Bool

canonicalGoldbachHaltingCompilerBoundary : GoldbachHaltingCompilerBoundary
canonicalGoldbachHaltingCompilerBoundary =
  goldbachHaltingCompilerBoundary
    true true false false false false
