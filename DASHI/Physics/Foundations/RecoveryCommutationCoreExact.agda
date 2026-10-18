{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.RecoveryCommutationCoreExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.BianchiLovelockCompletion as GR
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.RecoveredGRAttachmentExact as GRAttach
import DASHI.Physics.Foundations.PinnedYangMillsRecoveredQFTAttachmentExact as QFTAttach
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned

------------------------------------------------------------------------
-- SAME-OBJECT RECOVERY MATHEMATICS WITHOUT PROMOTION PAYLOAD
------------------------------------------------------------------------

record GRRecoveryCommutationCore (U : Weld.UnifiedCandidate) : Set₁ where
  field
    grRecoveryCommutes :
      ∀ candidate →
      Weld.recoverGR U (Weld.microscopicState U candidate)
      ≡ Weld.grTarget U candidate

    grRecoveryAfterCoarseGrainingCommutes :
      ∀ candidate regime →
      Weld.grRegime U regime →
      Weld.recoverGR U
        (Weld.microscopicState U (Weld.coarseGrain U candidate regime))
      ≡ Weld.grTarget U (Weld.coarseGrain U candidate regime)

open GRRecoveryCommutationCore public

record QFTRecoveryCommutationCore (U : Weld.UnifiedCandidate) : Set₁ where
  field
    qftRecoveryCommutes :
      ∀ candidate →
      Weld.recoverQFT U (Weld.microscopicState U candidate)
      ≡ Weld.qftTarget U candidate

    qftRecoveryAfterCoarseGrainingCommutes :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Weld.recoverQFT U
        (Weld.microscopicState U (Weld.coarseGrain U candidate regime))
      ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)

open QFTRecoveryCommutationCore public

grReceiptToCommutationCore :
  ∀ {U : Weld.UnifiedCandidate} →
  Weld.GRRecoveryReceipt U →
  GRRecoveryCommutationCore U
grReceiptToCommutationCore receipt = record
  { GRRecoveryCommutationCore.grRecoveryCommutes =
      Weld.grRecoveryCommutes receipt
  ; GRRecoveryCommutationCore.grRecoveryAfterCoarseGrainingCommutes =
      Weld.grRecoveryAfterCoarseGrainingCommutes receipt
  }

qftReceiptToCommutationCore :
  ∀ {U : Weld.UnifiedCandidate} →
  Weld.QFTRecoveryReceipt U →
  QFTRecoveryCommutationCore U
qftReceiptToCommutationCore receipt = record
  { QFTRecoveryCommutationCore.qftRecoveryCommutes =
      Weld.qftRecoveryCommutes receipt
  ; QFTRecoveryCommutationCore.qftRecoveryAfterCoarseGrainingCommutes =
      Weld.qftRecoveryAfterCoarseGrainingCommutes receipt
  }

recoveredGRAttachmentWithCommutationCore :
  ∀ {U : Weld.UnifiedCandidate}
    {G : GR.EinsteinContinuumClosure} →
  GRAttach.RecoveredGRAttachment U G →
  GRRecoveryCommutationCore U →
  ∀ candidate regime →
  Weld.grRegime U regime →
  G ≡ Weld.grTarget U (Weld.coarseGrain U candidate regime)
recoveredGRAttachmentWithCommutationCore attachment core candidate regime grAtRegime =
  trans
    (GRAttach.literalConstructionIsRecoveredGR
      attachment candidate regime grAtRegime)
    (grRecoveryAfterCoarseGrainingCommutes
      core candidate regime grAtRegime)

pinnedQFTAttachmentWithCommutationCore :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} →
  QFTAttach.PinnedYangMillsRecoveredQFTAttachment U pinned →
  QFTRecoveryCommutationCore U →
  ∀ candidate regime →
  Weld.qftRegime U regime →
  Pinned.asLiteralYangMillsConstruction pinned
  ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)
pinnedQFTAttachmentWithCommutationCore attachment core candidate regime qftAtRegime =
  trans
    (QFTAttach.literalPinnedConstructionIsRecoveredQFT
      attachment candidate regime qftAtRegime)
    (qftRecoveryAfterCoarseGrainingCommutes
      core candidate regime qftAtRegime)

fullGRRecoveryReceiptRequiredForSameObjectEquality : Bool
fullGRRecoveryReceiptRequiredForSameObjectEquality = false

fullGRRecoveryReceiptRequiredForSameObjectEqualityIsFalse :
  fullGRRecoveryReceiptRequiredForSameObjectEquality ≡ false
fullGRRecoveryReceiptRequiredForSameObjectEqualityIsFalse = refl

fullQFTRecoveryReceiptRequiredForSameObjectEquality : Bool
fullQFTRecoveryReceiptRequiredForSameObjectEquality = false

fullQFTRecoveryReceiptRequiredForSameObjectEqualityIsFalse :
  fullQFTRecoveryReceiptRequiredForSameObjectEquality ≡ false
fullQFTRecoveryReceiptRequiredForSameObjectEqualityIsFalse = refl
