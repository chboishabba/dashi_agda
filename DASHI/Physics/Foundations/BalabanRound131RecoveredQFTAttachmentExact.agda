{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanRound131RecoveredQFTAttachmentExact where

------------------------------------------------------------------------
-- ROUND131 / RECOVERED-QFT SAME-OBJECT ATTACHMENT
--
-- RSA-style proof-engineering rule:
--   recover the exact carrier on both sides, prove the equality, then transport.
--
-- Round131 already owns the continuum first-variation/stress theorem for one
-- fixed literal Yang--Mills construction Y.  The unified candidate separately
-- owns recoverQFT and a QFTRecoveryReceipt.  The first live unification seam is
-- therefore not another continuum theorem: it is the theorem-bearing equality
--
--   Y = recoverQFT (microscopicState (coarseGrain candidate regime)).
--
-- Once that equality is supplied, the existing recovery receipt transports it
-- to qftTarget.  This module names only that same-object socket and compiler.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record Round131RecoveredQFTAttachment
    (U : Weld.UnifiedCandidate)
    (Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)) : Set₁ where
  field
    literalConstructionIsRecoveredQFT :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      Y ≡ Weld.recoverQFT U
        (Weld.microscopicState U (Weld.coarseGrain U candidate regime))

open Round131RecoveredQFTAttachment public

recoveredAttachmentImpliesSelectedQFTTarget :
  ∀ {U : Weld.UnifiedCandidate}
    {Y : Top.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)} →
  Round131RecoveredQFTAttachment U Y →
  Weld.QFTRecoveryReceipt U →
  ∀ candidate regime →
  Weld.qftRegime U regime →
  Y ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)
recoveredAttachmentImpliesSelectedQFTTarget
    attachment qftRecovery candidate regime qftAtRegime =
  trans
    (literalConstructionIsRecoveredQFT
      attachment candidate regime qftAtRegime)
    (Weld.qftRecoveryAfterCoarseGrainingCommutes
      qftRecovery candidate regime qftAtRegime)

round131RecoveredQFTAttachmentCompilerLevel : ProofLevel
round131RecoveredQFTAttachmentCompilerLevel = machineChecked

-- The compiler is closed, but the physical/same-object attachment itself is
-- intentionally not manufactured here.
recoveredQFTConstructionAttachmentStillRequired : Bool
recoveredQFTConstructionAttachmentStillRequired = true

recoveredQFTConstructionAttachmentStillRequiredIsTrue :
  recoveredQFTConstructionAttachmentStillRequired ≡ true
recoveredQFTConstructionAttachmentStillRequiredIsTrue = refl
