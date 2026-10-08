module DASHI.Biology.AutismVaccineStrictBindingInstantiationExact where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AutismVaccineClaimPromotionAuditExact as Audit
import DASHI.Biology.StrictEvidencePromotionBindingExact as Strict

------------------------------------------------------------------------
-- CONCRETE STRICT BINDINGS
--
-- These values demonstrate the new same-object owner on exact claim/evidence
-- objects.  The key equalities are definitional and therefore cannot be paid by
-- an unrelated claim or evidence receipt without changing the indexed type.
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
    "Bounded no-association estimand reference; this is not a universal zero-risk theorem."

hviidPaysHbombNoLinkClaim :
  Strict.StrictPromotionBinding
    Audit.claimKey
    Audit.evidenceKey
    scopeKey
    Audit.hbombMMRNoLinkClaim
    Audit.hviid2019Receipt
    mmrAutismPopulationEstimand
hviidPaysHbombNoLinkClaim =
  Strict.strict-promotion-binding
    "hbomb-mmr-autism-no-link" refl
    "hviid-2019-danish-mmr-autism" refl
    "MMR-exposure / autism-diagnosis / nationwide-Danish-population / cohort-follow-up" refl
    "The independent Hviid receipt supports the bounded content of Hbomberguy's no-link claim; provenance remains independent."
    "Population, exposure, outcome and follow-up are carried by the bounded estimand reference rather than inferred from citation identity."
    "Observational cohort no-association; no causal sufficiency is promoted."

cochranePaysHbombNoLinkClaim :
  Strict.StrictPromotionBinding
    Audit.claimKey
    Audit.evidenceKey
    scopeKey
    Audit.hbombMMRNoLinkClaim
    Audit.cochrane2020Receipt
    mmrAutismPopulationEstimand
cochranePaysHbombNoLinkClaim =
  Strict.strict-promotion-binding
    "hbomb-mmr-autism-no-link" refl
    "cochrane-2020-mmr-autism" refl
    "MMR-exposure / autism-diagnosis / nationwide-Danish-population / cohort-follow-up" refl
    "The Cochrane receipt independently corroborates the bounded MMR/autism no-association reading; it is not attributed to Hbomberguy."
    "The review and cohort have different study aggregation structures; this shared scope key records the question, not identity of design."
    "Systematic-review evidence; no unrelated vaccine/outcome transport."

retractionPaysRetractionClaim :
  Strict.StrictPromotionPair
    Audit.claimKey
    Audit.evidenceKey
    Audit.hbombWakefieldRetractionClaim
    Audit.lancetRetractionReceipt
retractionPaysRetractionClaim =
  Strict.strict-promotion-pair
    "hbomb-wakefield-paper-retracted" refl
    "lancet-2010-retraction" refl
    "Independent retraction record pays the video's retraction statement."
    "Publication-status fact is bound to the retraction claim only; it does not pay MMR/autism causality."

bmjPaysFraudClaim :
  Strict.StrictPromotionPair
    Audit.claimKey
    Audit.evidenceKey
    Audit.hbombFraudClaim
    Audit.bmjFraudReceipt
bmjPaysFraudClaim =
  Strict.strict-promotion-pair
    "hbomb-wakefield-fraud" refl
    "bmj-2011-fraud-investigation" refl
    "Independent BMJ investigation pays a bounded fraud/misconduct reading."
    "Fraud evidence remains separate from epidemiologic no-association evidence."
