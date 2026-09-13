module DASHI.Law.SensibLawLegalReasonablenessRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawLegalReasonablenessExact as LR

wednesbury-appeal-was-dismissed :
  LR.wednesburyAppealDismissed LR.canonicalWednesburyCaseReceipt ≡ true
wednesbury-appeal-was-dismissed = refl

li-refusal-held-unreasonable :
  LR.liTribunalRefusalHeldLegallyUnreasonable LR.canonicalLiCaseReceipt ≡ true
li-refusal-held-unreasonable = refl

szvfw-tribunal-decision-not-held-unreasonable :
  LR.szvfwTribunalDecisionHeldLegallyUnreasonable LR.canonicalSZVFWCaseReceipt ≡ false
szvfw-tribunal-decision-not-held-unreasonable = refl

wednesbury-is-not-all-australian-unreasonableness :
  LR.wednesburyFormulationDefinitionallyExhaustsAustralianLegalUnreasonableness
    LR.canonicalLegalReasonablenessBoundary ≡ false
wednesbury-is-not-all-australian-unreasonableness = refl

merits-disagreement-does-not-prove-legal-unreasonableness :
  LR.meritsDisagreementAutomaticallyLegalUnreasonableness
    LR.canonicalLegalReasonablenessBoundary ≡ false
merits-disagreement-does-not-prove-legal-unreasonableness = refl

relevant-considerations-ground-is-not-definitionally-identical :
  LR.relevantConsiderationsGroundDefinitionallyLegalUnreasonableness
    LR.canonicalLegalReasonablenessBoundary ≡ false
relevant-considerations-ground-is-not-definitionally-identical = refl
