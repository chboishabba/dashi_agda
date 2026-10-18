{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.RecoveredGRAttachmentExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.BianchiLovelockCompletion as GR
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld

------------------------------------------------------------------------
-- RECOVERED-GR SAME-OBJECT ATTACHMENT
--
-- Exact analogue of the Round131 recovered-QFT attachment:
--
--   literal GR construction G
--     = recoverGR(microscopicState(coarseGrain candidate regime))
--     -> grTarget(coarseGrain candidate regime)
--
-- The second arrow is compiler output from GRRecoveryReceipt.  The physical
-- same-object equality remains the only primitive attachment.
------------------------------------------------------------------------

record RecoveredGRAttachment
    (U : Weld.UnifiedCandidate)
    (G : GR.EinsteinContinuumClosure) : Set₁ where
  field
    literalConstructionIsRecoveredGR :
      ∀ candidate regime →
      Weld.grRegime U regime →
      G ≡ Weld.recoverGR U
        (Weld.microscopicState U
          (Weld.coarseGrain U candidate regime))

open RecoveredGRAttachment public

recoveredAttachmentImpliesSelectedGRTarget :
  ∀ {U : Weld.UnifiedCandidate}
    {G : GR.EinsteinContinuumClosure} →
  RecoveredGRAttachment U G →
  Weld.GRRecoveryReceipt U →
  ∀ candidate regime →
  Weld.grRegime U regime →
  G ≡ Weld.grTarget U (Weld.coarseGrain U candidate regime)
recoveredAttachmentImpliesSelectedGRTarget
    attachment grRecovery candidate regime grAtRegime =
  trans
    (literalConstructionIsRecoveredGR
      attachment candidate regime grAtRegime)
    (Weld.grRecoveryAfterCoarseGrainingCommutes
      grRecovery candidate regime grAtRegime)

directSelectedGRTargetEqualityPrimitive : Bool
directSelectedGRTargetEqualityPrimitive = false

directSelectedGRTargetEqualityPrimitiveIsFalse :
  directSelectedGRTargetEqualityPrimitive ≡ false
directSelectedGRTargetEqualityPrimitiveIsFalse = refl

recoveredGRConstructionAttachmentStillRequired : Bool
recoveredGRConstructionAttachmentStillRequired = true

recoveredGRConstructionAttachmentStillRequiredIsTrue :
  recoveredGRConstructionAttachmentStillRequired ≡ true
recoveredGRConstructionAttachmentStillRequiredIsTrue = refl
