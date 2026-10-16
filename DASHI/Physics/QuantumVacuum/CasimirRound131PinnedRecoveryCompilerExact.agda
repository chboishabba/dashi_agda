module DASHI.Physics.QuantumVacuum.CasimirRound131PinnedRecoveryCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.BalabanRound131RecoveredQFTAttachmentExact as Round131
import DASHI.Physics.Foundations.PinnedYangMillsRecoveredQFTAttachmentExact as PinnedAttachment
import DASHI.Physics.Foundations.GRQFTSourceNativeQFTRecoveryProvenanceExact as Recovery
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned

------------------------------------------------------------------------
-- ROUND131 RECOVERED CONSTRUCTION + PINNED IDENTITY -> PINNED RECOVERY
--
-- The source-native host used to retain a separate
-- PinnedSourceNativeRecoverySelection payment after the Round131 recovered-QFT
-- attachment.  That duplicates the same equality once the literal R457
-- construction Y is identified with the pinned physical construction.
--
-- Inputs:
--   Y = recoverQFT(microscopicState(coarseGrain candidate regime))
--   Y = asLiteralYangMillsConstruction pinned
--
-- Compiler outputs:
--   asLiteralYangMillsConstruction pinned = recoverQFT(...)
--   PinnedYangMillsRecoveredQFTAttachment U pinned
--   PinnedSourceNativeRecoverySelection on the canonical formal projection.
--
-- Hence the real second payment is the same-object identity Y = pinned, not an
-- additional recovery-selection theorem.
------------------------------------------------------------------------

record R457LiteralPinnedConstructionIdentity
    (U : Weld.UnifiedCandidate)
    (Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U))
    (pinned : Pinned.PinnedYangMillsConstruction
      {C = Weld.qftCarriers U} (Weld.qftSemantics U)) : Set₁ where
  field
    r457LiteralIsPinned :
      Y ≡ Pinned.asLiteralYangMillsConstruction pinned

open R457LiteralPinnedConstructionIdentity public

round131AndPinnedIdentityBuildPinnedAttachment :
  ∀ {U : Weld.UnifiedCandidate}
    {Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {pinned : Pinned.PinnedYangMillsConstruction
      {C = Weld.qftCarriers U} (Weld.qftSemantics U)} →
  Round131.Round131RecoveredQFTAttachment U Y →
  R457LiteralPinnedConstructionIdentity U Y pinned →
  PinnedAttachment.PinnedYangMillsRecoveredQFTAttachment U pinned
round131AndPinnedIdentityBuildPinnedAttachment attachment identity = record
  { PinnedAttachment.PinnedYangMillsRecoveredQFTAttachment.literalPinnedConstructionIsRecoveredQFT =
      λ candidate regime qftAtRegime →
        trans
          (sym (r457LiteralIsPinned identity))
          (Round131.literalConstructionIsRecoveredQFT
            attachment candidate regime qftAtRegime)
  }

round131AndPinnedIdentityBuildSourceNativeSelection :
  ∀ {U : Weld.UnifiedCandidate}
    {Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {pinned : Pinned.PinnedYangMillsConstruction
      {C = Weld.qftCarriers U} (Weld.qftSemantics U)} →
  Round131.Round131RecoveredQFTAttachment U Y →
  R457LiteralPinnedConstructionIdentity U Y pinned →
  Recovery.PinnedSourceNativeRecoverySelection
    U pinned Recovery.canonicalFormalLegacyProjectionCompatibility
round131AndPinnedIdentityBuildSourceNativeSelection attachment identity = record
  { Recovery.PinnedSourceNativeRecoverySelection.enrichedMicroscopicStateIsPinned =
      λ candidate regime qftAtRegime →
        trans
          (sym
            (Round131.literalConstructionIsRecoveredQFT
              attachment candidate regime qftAtRegime))
          (r457LiteralIsPinned identity)
  }

round131AndPinnedIdentityBuildSelectedTargetEquality :
  ∀ {U : Weld.UnifiedCandidate}
    {Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {pinned : Pinned.PinnedYangMillsConstruction
      {C = Weld.qftCarriers U} (Weld.qftSemantics U)} →
  Round131.Round131RecoveredQFTAttachment U Y →
  R457LiteralPinnedConstructionIdentity U Y pinned →
  Weld.QFTRecoveryReceipt U →
  ∀ candidate regime →
  Weld.qftRegime U regime →
  Pinned.asLiteralYangMillsConstruction pinned
  ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)
round131AndPinnedIdentityBuildSelectedTargetEquality
    attachment identity qftRecovery candidate regime qftAtRegime =
  trans
    (PinnedAttachment.literalPinnedConstructionIsRecoveredQFT
      (round131AndPinnedIdentityBuildPinnedAttachment attachment identity)
      candidate regime qftAtRegime)
    (Weld.qftRecoveryAfterCoarseGrainingCommutes
      qftRecovery candidate regime qftAtRegime)

------------------------------------------------------------------------
-- Fail-closed status.
------------------------------------------------------------------------

data Round131RecoveryAutomaticallyIdentifiesPinnedPhysicalConstruction : Set where

round131RecoveryDoesNotIdentifyPinnedPhysicalConstruction :
  Round131RecoveryAutomaticallyIdentifiesPinnedPhysicalConstruction → ⊥
round131RecoveryDoesNotIdentifyPinnedPhysicalConstruction ()

record CasimirRound131PinnedRecoveryBoundary : Set where
  constructor casimir-round131-pinned-recovery-boundary
  field
    round131AndPinnedIdentityBuildPinnedAttachmentCompilerOwned : Bool
    pinnedSourceNativeSelectionCompilerOwned : Bool
    independentPinnedSourceNativeSelectionRequiredAfterInputs : Bool
    round131RecoveredQFTAttachmentStillRequired : Bool
    r457LiteralPinnedConstructionIdentityStillRequired : Bool

open CasimirRound131PinnedRecoveryBoundary public

canonicalRound131PinnedRecoveryBoundary : CasimirRound131PinnedRecoveryBoundary
canonicalRound131PinnedRecoveryBoundary =
  casimir-round131-pinned-recovery-boundary true true false true true

casimirRound131PinnedRecoveryReading : String
casimirRound131PinnedRecoveryReading =
  "Once the existing Round131RecoveredQFTAttachment is instantiated on the literal R457 construction Y, a single same-object identity Y = asLiteralYangMillsConstruction pinned compiles both the pinned recovered-QFT attachment and the former PinnedSourceNativeRecoverySelection. Therefore pinned source-native selection is not an independent host theorem. The live payments are the Round131 recovered-QFT attachment itself and identification of that SAME R457 literal construction with the existing pinned physical Yang-Mills construction."
