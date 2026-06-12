module DASHI.Physics.Probes.CurrentProofProfilePromotionProbe where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.CurrentProofProfileReceipt as Root

record CurrentProofProfilePromotionContract : Set where
  field
    ymCandidateCompleteNow :
      Root.ymCandidateCompleteNow Root.canonicalCurrentProofProfileReceipt ≡ true

currentProofProfilePromotionProbe : CurrentProofProfilePromotionContract
currentProofProfilePromotionProbe =
  record
    { ymCandidateCompleteNow = refl
    }
