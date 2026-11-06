module DASHI.Law.SensibLawWoogarooEPBC158AListingEventCut20261106Exact where

-- EPBC 2019/8575: source-typed statutory section 158A firewall.
--
-- AUTHORITATIVE: EPBC Act 1999 s 158A(1)(k),(2),(3),(4),(5), current
-- official compilation 1 July 2026, and the Commonwealth's 2010
-- Policy Statement "Listing Events under the EPBC Act". This section
-- pre-exists the 2020 controlled-action decision.
--
-- Source chronology: proponent/consultant PD says section 75 controlled
-- action determined 9 April 2020; official 2026 Commonwealth preliminary
-- documentation notice confirms earlier controlled-action determination
-- but not the original exact-day section 75 instrument. Commonwealth
-- listed koala QLD/NSW/ACT Endangered on 12 February 2022.
-- Approval signed Mark Hall 16 October 2026.
--
-- CONSEQUENCE: a post-section75 change from Vulnerable to Endangered
-- ordinarily is a "listing event" under s158A(1)(k) and is to be
-- disregarded in subsequent Part 7-9 approval decisions for SAME action.
-- Thus the hypothetical 1.2% Endangered OAG input (88.8287572%)
-- is a PHYSICAL CONSERVATION RISK SENSITIVITY, *not*, standing alone,
-- evidence the delegate was legally required to change a 2019/2020
-- Vulnerable-input OAG for its 2026 Part 9 decision.
--
-- Remains source-gated: obtain original s75 dated instrument, actual
-- accepted October OAG / relevant saved law, and identify any distinct
-- statutory defect not caused solely by the listing event.
--
-- The signed original QUT/QCC submissions are independent authored
-- critiques, not invented statute/court decisions. No litigation filed.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Law.SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact as Koala

data Event : Set where
  controlledDecision20200409 koalaUplisting20220212
    signedApproval20261016 : Event

data Authority : Set where
  publishedOriginalAct sourceAuthoredConsultantPD
    contemporaryOfficialListing originalSection75Instrument : Authority

record DatedClaim : Set where
  constructor dated-claim
  field
    dayYYYYMMDD : Nat
    event : Event
    attributedTo : Authority
    exactInstrumentObtained : Bool
open DatedClaim public

controlledDecision : DatedClaim
controlledDecision = dated-claim 20200409 controlledDecision20200409
  sourceAuthoredConsultantPD false

uplist : DatedClaim
uplist = dated-claim 20220212 koalaUplisting20220212
  contemporaryOfficialListing true

finalApproval : DatedClaim
finalApproval = dated-claim 20261016 signedApproval20261016
  publishedOriginalAct true

data StatutoryRoute : Set where
  section158AListingEventFirewall ordinaryScientificOAGScrutiny
    changedActionReReferral : StatutoryRoute

record ApplicableRoute : Set where
  constructor applicable-route
  field
    route : StatutoryRoute
    sameEPBCAction : Bool
    originalSection75DecisionBeforeUplisting : Bool
    higherThreatCategoryAfterDecision : Bool
    legalValidityChallengeFromUplistingAloneAvailable : Bool
    exceptionalEcologicalGainStillRequiresEvidence : Bool
open ApplicableRoute public

woogarooUplistingRoute : ApplicableRoute
woogarooUplistingRoute = applicable-route
  section158AListingEventFirewall
  true true true false true

noAutomaticStatusBasedInvalidity :
  legalValidityChallengeFromUplistingAloneAvailable
    woogarooUplistingRoute ≡ false
noAutomaticStatusBasedInvalidity = refl

doesNotRemoveScientificOffsetReview :
  exceptionalEcologicalGainStillRequiresEvidence
    woogarooUplistingRoute ≡ true
doesNotRemoveScientificOffsetReview = refl

-- These are conditional typed consequences of exact source record
-- interpretation, not Agda proving law applies to a real case. The
-- unacquired original s75 instrument is explicitly source stage FALSE.
section75OriginalStillUnacquired :
  exactInstrumentObtained controlledDecision ≡ false
section75OriginalStillUnacquired = refl

-- Original counterfactual remains a mathematical result only.
reusedPhysicalRiskCalculationCoefficient :
  Koala.inputSum Koala.allRows ≡ 1010350
reusedPhysicalRiskCalculationCoefficient = Koala.sourceWeightSum
