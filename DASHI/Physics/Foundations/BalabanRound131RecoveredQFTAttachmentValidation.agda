{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanRound131RecoveredQFTAttachmentValidation where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.BalabanRound131RecoveredQFTAttachmentExact as Attachment
import DASHI.Physics.Foundations.BalabanRound131RecoveredQFTTransportCompilerExact as Transport

-- Focused validation surface for the RSA-style same-carrier rule:
-- the first live unification seam is the exact attachment
--
--   Round131 literal construction Y
--     = recoverQFT (microscopicState (coarseGrain candidate regime)).
--
-- This file does not manufacture that equality.  It validates the named
-- same-object socket, the recovery-receipt compiler to qftTarget, and the
-- preferred compiler into the existing Round131 native-sector transport data.

round131RecoveredQFTAttachmentCompilerLevel : ProofLevel
round131RecoveredQFTAttachmentCompilerLevel =
  Attachment.round131RecoveredQFTAttachmentCompilerLevel

round131RecoveredQFTTransportCompilerLevel : ProofLevel
round131RecoveredQFTTransportCompilerLevel =
  Transport.round131RecoveredQFTTransportCompilerLevel

round131RecoveredQFTAttachmentStillRequired : Bool
round131RecoveredQFTAttachmentStillRequired =
  Attachment.recoveredQFTConstructionAttachmentStillRequired

round131RecoveredQFTAttachmentStillRequiredIsTrue :
  round131RecoveredQFTAttachmentStillRequired ≡ true
round131RecoveredQFTAttachmentStillRequiredIsTrue = refl

directSelectedQFTTargetEqualityPrimitive : Bool
directSelectedQFTTargetEqualityPrimitive =
  Transport.directSelectedQFTTargetEqualityPrimitive

directSelectedQFTTargetEqualityPrimitiveIsFalse :
  directSelectedQFTTargetEqualityPrimitive ≡ false
directSelectedQFTTargetEqualityPrimitiveIsFalse = refl
