module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetPolicyDecision where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel as Retargeted
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlNextIngredientGap as Gap

------------------------------------------------------------------------
-- W1d: explicit repo policy decision for the retargeted MDL channel.
--
-- This is intentionally narrow: the repo accepts exactly the canonical
-- transported schedule-MDL channel as the intended replacement noncanonical
-- MDL target.  It does not revive the obstructed current noncanonical carrier
-- and does not assert CR-flatness of that old carrier.

CanonicalRetargetPolicyPredicate :
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetedChannel →
  Set
CanonicalRetargetPolicyPredicate channel =
  channel
  ≡
  Retargeted.canonicalToNoncanonicalMdlCRRetargetedChannel

canonicalRetargetPolicyAssumption :
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAssumption
canonicalRetargetPolicyAssumption =
  record
    { acceptsTransportedScheduleAsIntendedNoncanonicalMdlTarget =
        CanonicalRetargetPolicyPredicate
    }

canonicalRetargetPolicyAcceptsCanonicalChannel :
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAssumption.acceptsTransportedScheduleAsIntendedNoncanonicalMdlTarget
    canonicalRetargetPolicyAssumption
    Retargeted.canonicalToNoncanonicalMdlCRRetargetedChannel
canonicalRetargetPolicyAcceptsCanonicalChannel =
  refl

canonicalToNoncanonicalMdlCRRetargetPolicyIngredient :
  Gap.CanonicalToNoncanonicalMdlCRRetargetPolicyIngredient
canonicalToNoncanonicalMdlCRRetargetPolicyIngredient =
  record
    { policyAssumption =
        canonicalRetargetPolicyAssumption
    ; acceptsRetargetedChannel =
        canonicalRetargetPolicyAcceptsCanonicalChannel
    }

canonicalToNoncanonicalMdlCRRetargetPolicyAccepted :
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted
canonicalToNoncanonicalMdlCRRetargetPolicyAccepted =
  Gap.CanonicalToNoncanonicalMdlNextIngredientGap.crRetargetPolicyAcceptanceFromIngredient
    Gap.canonicalToNoncanonicalMdlNextIngredientGap
    canonicalToNoncanonicalMdlCRRetargetPolicyIngredient
