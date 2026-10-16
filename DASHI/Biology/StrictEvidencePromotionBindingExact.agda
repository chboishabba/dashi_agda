module DASHI.Biology.StrictEvidencePromotionBindingExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- STRICT SAME-OBJECT / SAME-SCOPE PROMOTION BINDING
--
-- Key equalities preserve stable externally visible identifiers. The actual
-- promotion obligations are proof-relevant relations indexed by the exact
-- claim/evidence/estimand objects; arbitrary narrative strings cannot pay them.
------------------------------------------------------------------------

record StrictPromotionBinding
    {Claim Evidence Estimand : Set}
    (claimKey : Claim → String)
    (evidenceKey : Evidence → String)
    (estimandScopeKey : Estimand → String)
    (evidencePaysClaim : Evidence → Claim → Set)
    (evidenceMatchesEstimand : Evidence → Estimand → Set)
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
    evidencePaysClaimWitness : evidencePaysClaim evidence claim
    evidenceMatchesEstimandWitness : evidenceMatchesEstimand evidence estimand
    identificationReference : String

open StrictPromotionBinding public

record StrictPromotionPair
    {Claim Evidence : Set}
    (claimKey : Claim → String)
    (evidenceKey : Evidence → String)
    (evidencePaysClaim : Evidence → Claim → Set)
    (claim : Claim)
    (evidence : Evidence) : Set where
  constructor strict-promotion-pair
  field
    pairClaimKey : String
    pairClaimKeyMatches : pairClaimKey ≡ claimKey claim
    pairEvidenceKey : String
    pairEvidenceKeyMatches : pairEvidenceKey ≡ evidenceKey evidence
    pairEvidencePaysClaimWitness : evidencePaysClaim evidence claim
    pairSameObjectReference : String

open StrictPromotionPair public
