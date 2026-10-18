{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PinnedYangMillsRecoveredQFTAttachmentExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned

------------------------------------------------------------------------
-- PINNED YM -> RECOVERED QFT -> SELECTED QFT, WITH STRESS FOR FREE
--
-- PinnedYangMillsConstruction chooses one continuum family and compiles the
-- literal Clay object from it. Therefore its local stress tensor is
-- definitionally the stress tensor of the compiled literal construction.
-- The only physical same-object seam requested here is:
--
--   asLiteralYangMillsConstruction pinned
--     = recoverQFT(microscopicState(coarseGrain candidate regime)).
------------------------------------------------------------------------

record PinnedYangMillsRecoveredQFTAttachment
    (U : Weld.UnifiedCandidate)
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)) : Set₁ where
  field
    literalPinnedConstructionIsRecoveredQFT :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Pinned.asLiteralYangMillsConstruction pinned
      ≡ Weld.recoverQFT U
          (Weld.microscopicState U
            (Weld.coarseGrain U candidate regime))

open PinnedYangMillsRecoveredQFTAttachment public

pinnedConstructionIsSelectedQFTTarget :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} →
  PinnedYangMillsRecoveredQFTAttachment U pinned →
  Weld.QFTRecoveryReceipt U →
  ∀ candidate regime →
  Weld.qftRegime U regime →
  Pinned.asLiteralYangMillsConstruction pinned
  ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)
pinnedConstructionIsSelectedQFTTarget
    attachment qftRecovery candidate regime qftAtRegime =
  trans
    (literalPinnedConstructionIsRecoveredQFT
      attachment candidate regime qftAtRegime)
    (Weld.qftRecoveryAfterCoarseGrainingCommutes
      qftRecovery candidate regime qftAtRegime)

pinnedStressIsLiteralStress :
  ∀ {U : Weld.UnifiedCandidate}
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U))
    group →
  Pinned.stressTensor (Pinned.local pinned) group
  ≡ Top.stressTensor (Pinned.asLiteralYangMillsConstruction pinned) group
pinnedStressIsLiteralStress pinned group = refl

pinnedStressIsActualSelectedQFTStress :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)}
    (attachment : PinnedYangMillsRecoveredQFTAttachment U pinned)
    (qftRecovery : Weld.QFTRecoveryReceipt U)
    candidate regime →
  Weld.qftRegime U regime →
  ∀ group →
  Pinned.stressTensor (Pinned.local pinned) group
  ≡ Weld.actualQFTStressTensor U
      (Weld.coarseGrain U candidate regime) group
pinnedStressIsActualSelectedQFTStress
    attachment qftRecovery candidate regime qftAtRegime group =
  cong
    (λ construction → Top.stressTensor construction group)
    (pinnedConstructionIsSelectedQFTTarget
      attachment qftRecovery candidate regime qftAtRegime)

pinnedSharedSectorStressIsActualSelectedQFTStress :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)}
    (attachment : PinnedYangMillsRecoveredQFTAttachment U pinned)
    (qftRecovery : Weld.QFTRecoveryReceipt U)
    candidate regime →
  Weld.qftRegime U regime →
  ∀ group →
  Weld.qftSectorStressToShared U group
      (Pinned.stressTensor (Pinned.local pinned) group)
  ≡ Weld.actualQFTSectorStressShared U
      (Weld.coarseGrain U candidate regime) group
pinnedSharedSectorStressIsActualSelectedQFTStress
    {U = U} attachment qftRecovery candidate regime qftAtRegime group =
  cong
    (Weld.qftSectorStressToShared U group)
    (pinnedStressIsActualSelectedQFTStress
      attachment qftRecovery candidate regime qftAtRegime group)

pinnedRecoveredQFTAttachmentCompilerLevel : ProofLevel
pinnedRecoveredQFTAttachmentCompilerLevel = machineChecked

secondQFTStressIdentificationRequired : Bool
secondQFTStressIdentificationRequired = false

secondQFTStressIdentificationRequiredIsFalse :
  secondQFTStressIdentificationRequired ≡ false
secondQFTStressIdentificationRequiredIsFalse = refl
