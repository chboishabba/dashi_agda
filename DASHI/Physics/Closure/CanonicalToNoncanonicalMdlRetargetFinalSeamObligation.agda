module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetFinalSeamObligation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel as Retargeted
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCurrentCarrierObstruction as CurrentCarrier
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetPolicyDecision as Policy
import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff

------------------------------------------------------------------------
-- W1e: final seam obligation after W1d policy acceptance.
--
-- W1d accepted exactly the transported schedule-MDL channel as the intended
-- replacement noncanonical MDL target.  This module records the narrow
-- remaining seam surface.  It does not promote the old current carrier and
-- does not assert that the old current carrier is CR-flat.

RetargetedFinalSeamReceipt :
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted →
  Set
RetargetedFinalSeamReceipt accepted =
  (x : _) →
  Retargeted.transportedScheduleMdlChannel x
    ≡
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetedChannel.replacementNoncanonicalMdl
    (Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted.channel
      accepted)
    x

RetargetedFinalSeamDownstreamHandoffCompatibility :
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted →
  Set
RetargetedFinalSeamDownstreamHandoffCompatibility _ =
  Handoff.ChemistryPhysicalHandoffPreReceipt.currentStatus
    Handoff.canonicalChemistryPhysicalHandoffPreReceipt
    ≡
  Handoff.retargetedQuotientPrePhysicalConsumerAvailable

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

canonicalRetargetedFinalSeamReceipt :
  RetargetedFinalSeamReceipt
    Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
canonicalRetargetedFinalSeamReceipt =
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted.acceptedReplacementIsTransportedSchedule
    Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted

canonicalRetargetedFinalSeamHandoffCompatibility :
  RetargetedFinalSeamDownstreamHandoffCompatibility
    Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
canonicalRetargetedFinalSeamHandoffCompatibility =
  refl

canonicalRetargetedFinalSeamReceiptFields :
  RetargetedFinalSeamReceiptFields
canonicalRetargetedFinalSeamReceiptFields =
  record
    { acceptedRetargetedTarget =
        Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    ; oldCurrentCarrierObstructionAcknowledged =
        CurrentCarrier.canonicalToNoncanonicalMdlCurrentCarrierObstruction
    ; acceptedTargetIsTransportedSchedule =
        canonicalRetargetedFinalSeamReceipt
    ; finalSeamReceipt =
        RetargetedFinalSeamReceipt
          Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    ; downstreamHandoffCompatibility =
        RetargetedFinalSeamDownstreamHandoffCompatibility
          Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    }

data RetargetedFinalSeamResidualField : Set where
  strictPhysicalPromotionNotClaimed :
    RetargetedFinalSeamResidualField
  oldCurrentCarrierCRFlatStillObstructed :
    RetargetedFinalSeamResidualField

record RetargetedFinalSeamObligationStatus : Setω where
  field
    w1dAcceptedByEquality :
      Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted

    currentCarrierStillObstructed :
      CurrentCarrier.CanonicalToNoncanonicalMdlCurrentCarrierObstruction

    finalSeamReceiptLanded :
      Set

    downstreamHandoffCompatibilityLanded :
      Set

    finalSeamReceiptWitness :
      finalSeamReceiptLanded

    downstreamHandoffCompatibilityWitness :
      downstreamHandoffCompatibilityLanded

    residualFields :
      List RetargetedFinalSeamResidualField

    statusBoundary :
      List String

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
    ; finalSeamReceiptLanded =
        RetargetedFinalSeamReceipt
          Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    ; downstreamHandoffCompatibilityLanded =
        RetargetedFinalSeamDownstreamHandoffCompatibility
          Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    ; finalSeamReceiptWitness =
        canonicalRetargetedFinalSeamReceipt
    ; downstreamHandoffCompatibilityWitness =
        canonicalRetargetedFinalSeamHandoffCompatibility
    ; residualFields =
        strictPhysicalPromotionNotClaimed
        ∷ oldCurrentCarrierCRFlatStillObstructed
        ∷ []
    ; statusBoundary =
        "W1 final seam receipt is the accepted transported schedule-MDL replacement equality"
        ∷ "Downstream handoff compatibility is only with the existing pre-physical chemistry handoff consumer"
        ∷ "No strict physical calibration, spectra, bonding, wet-lab, or empirical validation claim is made here"
        ∷ "The old current noncanonical carrier remains obstructed and no CR-flat claim is revived"
        ∷ []
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
