module DASHI.Biology.AutismVaccineStrictBindingInstantiationExact where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AutismVaccineClaimPromotionAuditExact as Audit
import DASHI.Biology.StrictEvidencePromotionBindingExact as Strict

------------------------------------------------------------------------
-- CONCRETE STRICT BINDINGS
--
-- The relations below have constructors only for the exact evidence/claim and
-- evidence/estimand pairs that are admitted.  Matching strings cannot forge a
-- witness for an unrelated object.
------------------------------------------------------------------------

record BoundedEstimandReference : Set where
  constructor bounded-estimand-reference
  field
    scopeKey : String
    reading : String

open BoundedEstimandReference public

mmrAutismPopulationEstimand : BoundedEstimandReference
mmrAutismPopulationEstimand =
  bounded-estimand-reference
    "MMR-exposure / autism-diagnosis / nationwide-Danish-population / cohort-follow-up"
    "Bounded no-association estimand for the Hviid nationwide Danish cohort; this is not a universal zero-risk theorem."

mmrAutismReviewEstimand : BoundedEstimandReference
mmrAutismReviewEstimand =
  bounded-estimand-reference
    "MMR-exposure / autism-outcome / included-review-studies / pooled-review-evidence"
    "Review-level no-association estimand bounded to the studies/populations included by the Cochrane review."

data EvidencePaysClaim : Audit.EvidenceReceipt → Audit.AttributedClaim → Set where
  hviidPaysNoLink : EvidencePaysClaim Audit.hviid2019Receipt Audit.hbombMMRNoLinkClaim
  cochranePaysNoLink : EvidencePaysClaim Audit.cochrane2020Receipt Audit.hbombMMRNoLinkClaim
  retractionPaysRetraction : EvidencePaysClaim Audit.lancetRetractionReceipt Audit.hbombWakefieldRetractionClaim
  bmjPaysFraud : EvidencePaysClaim Audit.bmjFraudReceipt Audit.hbombFraudClaim

data EvidenceMatchesEstimand : Audit.EvidenceReceipt → BoundedEstimandReference → Set where
  hviidMatchesPopulationEstimand :
    EvidenceMatchesEstimand Audit.hviid2019Receipt mmrAutismPopulationEstimand
  cochraneMatchesReviewEstimand :
    EvidenceMatchesEstimand Audit.cochrane2020Receipt mmrAutismReviewEstimand

hviidPaysHbombNoLinkClaim :
  Strict.StrictPromotionBinding
    Audit.claimKey
    Audit.evidenceKey
    scopeKey
    EvidencePaysClaim
    EvidenceMatchesEstimand
    Audit.hbombMMRNoLinkClaim
    Audit.hviid2019Receipt
    mmrAutismPopulationEstimand
hviidPaysHbombNoLinkClaim =
  Strict.strict-promotion-binding
    "hbomb-mmr-autism-no-link" refl
    "hviid-2019-danish-mmr-autism" refl
    "MMR-exposure / autism-diagnosis / nationwide-Danish-population / cohort-follow-up" refl
    hviidPaysNoLink
    hviidMatchesPopulationEstimand
    "Observational cohort no-association; population, exposure, outcome and follow-up remain indexed to the Hviid estimand and no causal sufficiency is promoted."

cochranePaysHbombNoLinkClaim :
  Strict.StrictPromotionBinding
    Audit.claimKey
    Audit.evidenceKey
    scopeKey
    EvidencePaysClaim
    EvidenceMatchesEstimand
    Audit.hbombMMRNoLinkClaim
    Audit.cochrane2020Receipt
    mmrAutismReviewEstimand
cochranePaysHbombNoLinkClaim =
  Strict.strict-promotion-binding
    "hbomb-mmr-autism-no-link" refl
    "cochrane-2020-mmr-autism" refl
    "MMR-exposure / autism-outcome / included-review-studies / pooled-review-evidence" refl
    cochranePaysNoLink
    cochraneMatchesReviewEstimand
    "Systematic-review evidence is bound to its own included-study review estimand; it cannot borrow the Danish-cohort population/design or transport to unrelated vaccines/outcomes."

retractionPaysRetractionClaim :
  Strict.StrictPromotionPair
    Audit.claimKey
    Audit.evidenceKey
    EvidencePaysClaim
    Audit.hbombWakefieldRetractionClaim
    Audit.lancetRetractionReceipt
retractionPaysRetractionClaim =
  Strict.strict-promotion-pair
    "hbomb-wakefield-paper-retracted" refl
    "lancet-2010-retraction" refl
    retractionPaysRetraction
    "Publication-status fact is proof-relevantly bound to the retraction claim only; it does not pay MMR/autism causality."

bmjPaysFraudClaim :
  Strict.StrictPromotionPair
    Audit.claimKey
    Audit.evidenceKey
    EvidencePaysClaim
    Audit.hbombFraudClaim
    Audit.bmjFraudReceipt
bmjPaysFraudClaim =
  Strict.strict-promotion-pair
    "hbomb-wakefield-fraud" refl
    "bmj-2011-fraud-investigation" refl
    bmjPaysFraud
    "Fraud/misconduct evidence is proof-relevantly bound to the fraud claim and remains separate from epidemiologic no-association evidence."
