module DASHI.ComputerScience.Goldbach30To29HaltingConsumerCompilerExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.Goldbach29ExternalHaltingSemanticsExact as External29
import DASHI.ComputerScience.Goldbach30HaltingSourceAuditExact as Audit30

------------------------------------------------------------------------
-- HALTING-CONSUMER COMPILER
--
-- Literal state identity or fine-state bisimulation is unnecessary if both
-- machines are independently proved to realize the SAME counterexample
-- consumer. This module pays that logical compiler exactly.
--
-- External source text is not silently turned into an Agda inhabitant. In
-- particular the pinned Goldbach29 semantic tree contains theorem text but its
-- Main/Loops duplicate/self-import anomaly means build-verified formal authority
-- is not yet paid at that revision.
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

goldbach29ExternalTheoremTextAvailable : Bool
goldbach29ExternalTheoremTextAvailable =
  External29.externalGoldbach29HaltingTheoremTextPresent

goldbach29ExternalSourceCanFillRightHandRole : Bool
goldbach29ExternalSourceCanFillRightHandRole =
  External29.externalGoldbach29SemanticTreeBuildAuthorityPaid

goldbach30NarrativeClaimExists : Bool
goldbach30NarrativeClaimExists = Audit30.goldbach30NarrativeHaltingClaimFound

goldbach30NarrativeClaimCanFillLeftHandRole : Bool
goldbach30NarrativeClaimCanFillLeftHandRole = false

-- Neither external lane currently supplies an Agda HaltingConsumerAttachment:
-- Goldbach29 theorem text is pinned but its semantic source tree has not earned
-- a clean build receipt; Goldbach30 has a signed narrative claim but no recovered
-- Main/Loops theorem source. The checkpoint theorem elsewhere in DASHI is a
-- separate native result and does not erase this cross-prover authority boundary.

goldbach30HaltingAttachmentPaid : Bool
goldbach30HaltingAttachmentPaid = false

goldbach29AgdaHaltingAttachmentPaid : Bool
goldbach29AgdaHaltingAttachmentPaid = false

record GoldbachHaltingCompilerBoundary : Set where
  constructor goldbachHaltingCompilerBoundary
  field
    sameConsumerCompilerPaid : Bool
    goldbach29TheoremTextAvailable : Bool
    goldbach29BuildVerifiedFormalSourceAvailable : Bool
    goldbach30NarrativeClaimAvailable : Bool
    goldbach30NarrativeClaimIsFormalSource : Bool
    goldbach29AgdaAttachmentAvailable : Bool
    goldbach30AttachmentAvailable : Bool
    literalFineStateIdentityRequiredForHaltingEquivalence : Bool
    fullWeakBisimulationRequiredIfSameConsumerAttachmentsExist : Bool

canonicalGoldbachHaltingCompilerBoundary : GoldbachHaltingCompilerBoundary
canonicalGoldbachHaltingCompilerBoundary =
  goldbachHaltingCompilerBoundary
    true true false true false false false false false
