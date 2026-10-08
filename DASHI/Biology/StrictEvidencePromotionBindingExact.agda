module DASHI.Biology.StrictEvidencePromotionBindingExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- STRICT SAME-OBJECT / SAME-SCOPE PROMOTION BINDING
--
-- This owner addresses the generic gap where a validation receipt and a causal
-- estimand can have compatible types yet belong to unrelated evidence.  A
-- strict binding is indexed by the exact claim/evidence/estimand values and
-- carries equality witnesses tying externally visible keys to those values.
------------------------------------------------------------------------

record StrictPromotionBinding
    {Claim Evidence Estimand : Set}
    (claimKey : Claim → String)
    (evidenceKey : Evidence → String)
    (estimandScopeKey : Estimand → String)
    (claim : Claim)
    (evidence : Evidence)
    (estimand : Estimand) : Set where
  constructor strict-promotion-binding
  field
    boundClaimKey : String
    boundClaimKeyMatches : boundClaimKey ≡ claimKey claim
    boundEvidenceKey : String
    boundEvidenceKeyMatches : boundEvidenceKey ≡ evidenceKey evidence
    boundEstimandScopeKey : String
    boundEstimandScopeKeyMatches : boundEstimandScopeKey ≡ estimandScopeKey estimand
    evidencePaysClaimReference : String
    estimandMatchesEvidenceScopeReference : String
    identificationReference : String

open StrictPromotionBinding public

record StrictPromotionPair
    {Claim Evidence : Set}
    (claimKey : Claim → String)
    (evidenceKey : Evidence → String)
    (claim : Claim)
    (evidence : Evidence) : Set where
  constructor strict-promotion-pair
  field
    pairClaimKey : String
    pairClaimKeyMatches : pairClaimKey ≡ claimKey claim
    pairEvidenceKey : String
    pairEvidenceKeyMatches : pairEvidenceKey ≡ evidenceKey evidence
    pairEvidencePaysClaimReference : String
    pairSameObjectReference : String

open StrictPromotionPair public
