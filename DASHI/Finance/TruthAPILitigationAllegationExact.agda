module DASHI.Finance.TruthAPILitigationAllegationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- TRUTH API LITIGATION SOURCE
--
-- The Intercept Media, Inc. and Freedom of the Press Foundation filed a federal
-- complaint on August 12, 2026 challenging paid advance access to official
-- government communications through Truth API.  A complaint is a primary source
-- for what the plaintiffs alleged and what relief they requested; it is not an
-- adjudicated finding that the allegations are true.
------------------------------------------------------------------------

courtComplaintArtifact : Source.SourceArtifact
courtComplaintArtifact =
  Source.sourceArtifact
    "The-Intercept-Media-v-Trump-SDNY-1-26-cv-06867-Dkt-1"
    Source.documentaryArtifact
    "https://www.courtlistener.com/docket/74637796/the-intercept-media-inc-v-trump/"
    "United States District Court for the Southern District of New York / RECAP"

truthAPIConstitutionalChallengeFiled : Atlas.TradeEvidenceClaim
truthAPIConstitutionalChallengeFiled =
  Atlas.tradeEvidenceClaim
    "Intercept-FPF-v-Trump-2026-08-12-complaint"
    "Donald J. Trump in his official capacity and other federal defendants"
    "Truth API / official-government-communication access challenge"
    Atlas.regulatoryConcernClaim
    "2026-08-12"
    "2026-08-12"
    "The Intercept Media, Inc. and Freedom of the Press Foundation filed a complaint in the Southern District of New York, case 1:26-cv-06867, alleging that the challenged Truth API/Truth Social arrangement violates the First and Fifth Amendments and seeking declaratory/injunctive relief. The filing proves the existence and content of the plaintiffs' allegations, not their merits."
    Atlas.attributedConcernSupport
    (Atlas.sourceCitation
      "The Intercept Media, Inc. and Freedom of the Press Foundation, plaintiffs"
      "Complaint — The Intercept Media, Inc. v. Trump, No. 1:26-cv-06867 (S.D.N.Y.), Dkt. 1"
      "2026-08-12"
      "no DOI"
      "https://www.courtlistener.com/docket/74637796/the-intercept-media-inc-v-trump/"
      Atlas.attributedRegulatoryConcern)
    courtComplaintArtifact
    "Pays filing identity, parties, causes asserted and requested relief as allegations in a pleading. It does not establish constitutional violation, corruption, securities violation, insider trading, customer identity or market effect."
    true false false false

truthAPIComplaintPricingAllegation : Atlas.TradeEvidenceClaim
truthAPIComplaintPricingAllegation =
  Atlas.tradeEvidenceClaim
    "Intercept-FPF-v-Trump-Truth-API-pricing-allegation"
    "The Intercept Media, Inc. and Freedom of the Press Foundation, plaintiffs"
    "Truth API subscription pricing"
    Atlas.informationLatencyClaim
    "alleged current pricing as of complaint"
    "2026-08-12"
    "Paragraph 56 of the complaint alleges Truth API access costs $100,000 per month or $60,000 per month for a three-year commitment. This is retained as a party allegation pending an independent contract/rate-card receipt."
    Atlas.attributedConcernSupport
    (Atlas.sourceCitation
      "The Intercept Media, Inc. and Freedom of the Press Foundation, plaintiffs"
      "Complaint — The Intercept Media, Inc. v. Trump, paragraph 56"
      "2026-08-12"
      "no DOI"
      "https://www.courtlistener.com/docket/74637796/the-intercept-media-inc-v-trump/"
      Atlas.attributedRegulatoryConcern)
    courtComplaintArtifact
    "Pays that the complaint makes the pricing allegation. It does not independently establish that these were the operative contract prices for every customer."
    true false false false

------------------------------------------------------------------------
-- Pleading / adjudication boundary.
------------------------------------------------------------------------

data FiledComplaintAutomaticallyProvesAllegation : Set where
data ConstitutionalAllegationAutomaticallyProvesSecuritiesViolation : Set where
data ComplaintPricingAutomaticallyPaysExecutedContract : Set where

complaintDoesNotProveItsAllegations :
  FiledComplaintAutomaticallyProvesAllegation → ⊥
complaintDoesNotProveItsAllegations ()

constitutionalClaimDoesNotProveSecuritiesViolation :
  ConstitutionalAllegationAutomaticallyProvesSecuritiesViolation → ⊥
constitutionalClaimDoesNotProveSecuritiesViolation ()

complaintPriceDoesNotPayExecutedContract :
  ComplaintPricingAutomaticallyPaysExecutedContract → ⊥
complaintPriceDoesNotPayExecutedContract ()

record TruthAPILitigationAllegationBoundary : Set where
  constructor truth-api-litigation-allegation-boundary
  field
    complaintIdentityPaid : Bool
    plaintiffAllegationContentPaid : Bool
    legalMeritsStillUnpaid : Bool
    securitiesViolationStillUnpaid : Bool
    executedCustomerContractStillUnpaid : Bool
    pricingRetainedAsAttributedAllegation : Bool

canonicalTruthAPILitigationAllegationBoundary :
  TruthAPILitigationAllegationBoundary
canonicalTruthAPILitigationAllegationBoundary =
  truth-api-litigation-allegation-boundary true true true true true true
