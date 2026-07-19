module DASHI.Foundations.CanonicalProvenancePromotionTests where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.CanonicalProvenancePromotion

severityExactIsInformational : severity exact ≡ informational
severityExactIsInformational = refl

severityPartialIsWarning : severity partial ≡ warning
severityPartialIsWarning = refl

severityNoTypedMeetIsBlocking : severity noTypedMeet ≡ blocking
severityNoTypedMeetIsBlocking = refl

severityContradictionIsInconsistent :
  severity contradiction ≡ inconsistent
severityContradictionIsInconsistent = refl

closedGateComputesTrue :
  allClosed (promotionObligations true true true true true) ≡ true
closedGateComputesTrue = refl

openGateComputesFalse :
  allClosed (promotionObligations true true false true true) ≡ false
openGateComputesFalse = refl

closedGatePromotes :
  promote (promotionObligations true true true true true) ≡ promoted
closedGatePromotes = refl

openGateQuarantines :
  promote (promotionObligations true true false true true)
    ≡ quarantinedStatus
openGateQuarantines = refl
