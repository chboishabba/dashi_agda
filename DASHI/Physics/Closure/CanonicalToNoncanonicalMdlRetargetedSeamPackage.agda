module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetedSeamPackage where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel as Retargeted
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetPolicyDecision as Policy
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetFinalSeamObligation as Final
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCurrentCarrierObstruction as Current

------------------------------------------------------------------------
-- Current canonical-to-noncanonical MDL theorem owner.
--
-- The global old-carrier CR target is not revived.  The accepted theorem is
-- the retargeted transported schedule-MDL channel, together with its final
-- seam equality and downstream pre-physical chemistry handoff.  The old
-- current carrier remains explicitly obstructed.

record CanonicalToNoncanonicalMdlRetargetedSeamPackage : Setω where
  field
    acceptedRetargetedChannel :
      Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted

    finalSeamFields :
      Final.RetargetedFinalSeamReceiptFields

    finalSeamStatus :
      Final.RetargetedFinalSeamObligationStatus

    oldCurrentCarrierObstruction :
      Current.CanonicalToNoncanonicalMdlCurrentCarrierObstruction

    claimBoundary : List String

canonicalToNoncanonicalMdlRetargetedSeamPackage :
  CanonicalToNoncanonicalMdlRetargetedSeamPackage
canonicalToNoncanonicalMdlRetargetedSeamPackage =
  record
    { acceptedRetargetedChannel =
        Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    ; finalSeamFields =
        Final.canonicalRetargetedFinalSeamReceiptFields
    ; finalSeamStatus =
        Final.canonicalRetargetedFinalSeamObligationStatus
    ; oldCurrentCarrierObstruction =
        Current.canonicalToNoncanonicalMdlCurrentCarrierObstruction
    ; claimBoundary =
        "The accepted noncanonical target is the transported schedule-MDL channel"
        ∷ "The final seam receipt and downstream pre-physical handoff are landed"
        ∷ "The old current carrier remains CR-obstructed"
        ∷ "No strict physical calibration or empirical promotion follows from this package"
        ∷ []
    }
