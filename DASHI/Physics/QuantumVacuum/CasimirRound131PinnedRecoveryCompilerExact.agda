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
-- R457 SELECTED-TARGET IDENTITY -> ROUND131 RECOVERY ATTACHMENT
------------------------------------------------------------------------

record R457LiteralSelectedQFTTargetIdentity
    (U : Weld.UnifiedCandidate)
    (Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)) : Set₁ where
  field
    r457LiteralIsSelectedTarget :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Y ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)

open R457LiteralSelectedQFTTargetIdentity public

selectedTargetIdentityBuildsRound131Attachment :
  ∀ {U : Weld.UnifiedCandidate}
    {Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)} →
  R457LiteralSelectedQFTTargetIdentity U Y →
  Weld.QFTRecoveryReceipt U →
  Round131.Round131RecoveredQFTAttachment U Y
selectedTargetIdentityBuildsRound131Attachment identity qftRecovery = record
  { Round131.Round131RecoveredQFTAttachment.literalConstructionIsRecoveredQFT =
      λ candidate regime qftAtRegime →
        trans
          (r457LiteralIsSelectedTarget identity candidate regime qftAtRegime)
          (sym
            (Weld.qftRecoveryAfterCoarseGrainingCommutes
              qftRecovery candidate regime qftAtRegime))
  }

------------------------------------------------------------------------
-- ROUND131 RECOVERED CONSTRUCTION + PINNED IDENTITY -> PINNED RECOVERY
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

selectedTargetAndPinnedIdentityBuildPinnedAttachment :
  ∀ {U : Weld.UnifiedCandidate}
    {Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {pinned : Pinned.PinnedYangMillsConstruction
      {C = Weld.qftCarriers U} (Weld.qftSemantics U)} →
  R457LiteralSelectedQFTTargetIdentity U Y →
  R457LiteralPinnedConstructionIdentity U Y pinned →
  Weld.QFTRecoveryReceipt U →
  PinnedAttachment.PinnedYangMillsRecoveredQFTAttachment U pinned
selectedTargetAndPinnedIdentityBuildPinnedAttachment
    selectedTarget identity qftRecovery =
  round131AndPinnedIdentityBuildPinnedAttachment
    (selectedTargetIdentityBuildsRound131Attachment selectedTarget qftRecovery)
    identity

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
round131AndPinnedIdentityBuildSourceNativeSelection
    {U = U} attachment identity = record
  { Recovery.PinnedSourceNativeRecoverySelection.enrichedMicroscopicStateIsPinned =
      λ candidate regime qftAtRegime →
        let joint = Weld.microscopicState U (Weld.coarseGrain U candidate regime)
        in
        trans
          (sym
            (Recovery.legacyRecoverAgreesWithSourceNative
              Recovery.canonicalFormalLegacyProjectionCompatibility joint))
          (trans
            (sym
              (Round131.literalConstructionIsRecoveredQFT
                attachment candidate regime qftAtRegime))
            (r457LiteralIsPinned identity))
  }

selectedTargetAndPinnedIdentityBuildSourceNativeSelection :
  ∀ {U : Weld.UnifiedCandidate}
    {Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {pinned : Pinned.PinnedYangMillsConstruction
      {C = Weld.qftCarriers U} (Weld.qftSemantics U)} →
  R457LiteralSelectedQFTTargetIdentity U Y →
  R457LiteralPinnedConstructionIdentity U Y pinned →
  Weld.QFTRecoveryReceipt U →
  Recovery.PinnedSourceNativeRecoverySelection
    U pinned Recovery.canonicalFormalLegacyProjectionCompatibility
selectedTargetAndPinnedIdentityBuildSourceNativeSelection
    selectedTarget identity qftRecovery =
  round131AndPinnedIdentityBuildSourceNativeSelection
    (selectedTargetIdentityBuildsRound131Attachment selectedTarget qftRecovery)
    identity

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

data SelectedTargetIdentityAutomaticallyFollowsFromQFTRecovery : Set where

data Round131RecoveryAutomaticallyIdentifiesPinnedPhysicalConstruction : Set where

selectedTargetIdentityDoesNotFollowFromQFTRecovery :
  SelectedTargetIdentityAutomaticallyFollowsFromQFTRecovery → ⊥
selectedTargetIdentityDoesNotFollowFromQFTRecovery ()

round131RecoveryDoesNotIdentifyPinnedPhysicalConstruction :
  Round131RecoveryAutomaticallyIdentifiesPinnedPhysicalConstruction → ⊥
round131RecoveryDoesNotIdentifyPinnedPhysicalConstruction ()

record CasimirRound131PinnedRecoveryBoundary : Set where
  constructor casimir-round131-pinned-recovery-boundary
  field
    selectedTargetIdentityBuildsRound131AttachmentCompilerOwned : Bool
    independentRound131RecoveredAttachmentRequiredAfterSelectedTargetIdentity : Bool
    r457LiteralSelectedQFTTargetIdentityStillRequired : Bool
    round131AndPinnedIdentityBuildPinnedAttachmentCompilerOwned : Bool
    pinnedSourceNativeSelectionCompilerOwned : Bool
    independentPinnedSourceNativeSelectionRequiredAfterInputs : Bool
    r457LiteralPinnedConstructionIdentityStillRequired : Bool

open CasimirRound131PinnedRecoveryBoundary public

canonicalRound131PinnedRecoveryBoundary : CasimirRound131PinnedRecoveryBoundary
canonicalRound131PinnedRecoveryBoundary =
  casimir-round131-pinned-recovery-boundary true false true true true false true

casimirRound131PinnedRecoveryReading : String
casimirRound131PinnedRecoveryReading =
  "QFTRecoveryReceipt already transports recoverQFT to qftTarget on every selected coarse-grained regime. Therefore Round131RecoveredQFTAttachment is no longer primitive: an R457LiteralSelectedQFTTargetIdentity Y=qftTarget plus the existing recovery receipt compiles it. On the generic compatibility route, adding Y=asLiteralYangMillsConstruction pinned compiles the pinned recovered-QFT attachment and former PinnedSourceNativeRecoverySelection. On the canonical pinned R457 route that extra Y=pinned equality is retired by indexing R457 directly by asLiteralYangMillsConstruction pinned."
