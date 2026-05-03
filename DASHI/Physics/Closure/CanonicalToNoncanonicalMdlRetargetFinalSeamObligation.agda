module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetFinalSeamObligation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel as Retargeted
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCurrentCarrierObstruction as CurrentCarrier
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetPolicyDecision as Policy

------------------------------------------------------------------------
-- W1e: final seam obligation after W1d policy acceptance.
--
-- W1d accepted exactly the transported schedule-MDL channel as the intended
-- replacement noncanonical MDL target.  This module records the narrow
-- remaining seam surface.  It does not promote the old current carrier and
-- does not assert that the old current carrier is CR-flat.

record RetargetedFinalSeamReceiptFields : Setω where
  field
    acceptedRetargetedTarget :
      Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted

    oldCurrentCarrierObstructionAcknowledged :
      CurrentCarrier.CanonicalToNoncanonicalMdlCurrentCarrierObstruction

    acceptedTargetIsTransportedSchedule :
      (x : _) →
      Retargeted.transportedScheduleMdlChannel x
        ≡
      Retargeted.CanonicalToNoncanonicalMdlCRRetargetedChannel.replacementNoncanonicalMdl
        (Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted.channel
          acceptedRetargetedTarget)
        x

    finalSeamReceipt :
      Set

    downstreamHandoffCompatibility :
      Set

record RetargetedFinalSeamObligationStatus : Setω where
  field
    w1dAcceptedByEquality :
      Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted

    currentCarrierStillObstructed :
      CurrentCarrier.CanonicalToNoncanonicalMdlCurrentCarrierObstruction

    finalSeamReceiptStillNeeded :
      Set

    downstreamHandoffCompatibilityStillNeeded :
      Set

    noOldCurrentCarrierCRFlatClaim :
      Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted →
      CurrentCarrier.CanonicalToNoncanonicalMdlCurrentCarrierObstruction →
      Set

canonicalRetargetedFinalSeamObligationStatus :
  RetargetedFinalSeamObligationStatus
canonicalRetargetedFinalSeamObligationStatus =
  record
    { w1dAcceptedByEquality =
        Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    ; currentCarrierStillObstructed =
        CurrentCarrier.canonicalToNoncanonicalMdlCurrentCarrierObstruction
    ; finalSeamReceiptStillNeeded =
        ⊥
    ; downstreamHandoffCompatibilityStillNeeded =
        ⊥
    ; noOldCurrentCarrierCRFlatClaim =
        λ _ _ → ⊥
    }

retargetedFinalSeamReceiptFromFields :
  RetargetedFinalSeamReceiptFields →
  Set
retargetedFinalSeamReceiptFromFields fields =
  RetargetedFinalSeamReceiptFields.finalSeamReceipt fields

retargetedFinalSeamHandoffFromFields :
  RetargetedFinalSeamReceiptFields →
  Set
retargetedFinalSeamHandoffFromFields fields =
  RetargetedFinalSeamReceiptFields.downstreamHandoffCompatibility fields
