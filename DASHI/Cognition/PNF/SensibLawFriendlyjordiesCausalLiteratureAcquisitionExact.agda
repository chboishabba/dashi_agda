module DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalLiteratureAcquisitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalIdentificationMaxCutExact as Causal

------------------------------------------------------------------------
-- Source-attributed causal-literature acquisition.
--
-- These are literature receipts, not causal-identification receipts. Each
-- record keeps authorship, method and target explicit so a methodologically
-- serious paper cannot silently pay a different political estimand.
------------------------------------------------------------------------

data LiteratureDesignClass : Set where
  syntheticControlDesign : LiteratureDesignClass
  interviewDocumentCaseStudy : LiteratureDesignClass
  carbonPriceAttributionEstimate : LiteratureDesignClass
  policyUncertaintyStructuralBreakStudy : LiteratureDesignClass

record CausalLiteratureCandidate (case : March.MarchCase) : Set where
  constructor causal-literature-candidate
  field
    sourceRef : String
    title : String
    authorsRef : String
    publicationRef : String
    methodRef : String
    targetRef : String
    designClass : LiteratureDesignClass
    relevantDemandRef : String

    sourceSupportsMethodDescription : Bool
    sourceSupportsMethodDescriptionIsTrue :
      sourceSupportsMethodDescription ≡ true
    sourceSupportsTargetDescription : Bool
    sourceSupportsTargetDescriptionIsTrue :
      sourceSupportsTargetDescription ≡ true

    exactGovernanceDemandMatch : Bool
    exactGovernanceDemandMatchIsFalse :
      exactGovernanceDemandMatch ≡ false
    admissibleIdentificationGatePaid : Bool
    admissibleIdentificationGatePaidIsFalse :
      admissibleIdentificationGatePaid ≡ false
    identifiesPartySpecificCause : Bool
    identifiesPartySpecificCauseIsFalse :
      identifiesPartySpecificCause ≡ false
    createsUniversalPartyRanking : Bool
    createsUniversalPartyRankingIsFalse :
      createsUniversalPartyRanking ≡ false

open CausalLiteratureCandidate public

------------------------------------------------------------------------
-- 2026 Australia policy-mix synthetic control.
--
-- Kraynak / Timilsina / Alberini estimate the joint effect of expanded RET
-- incentives and the 2012-14 Carbon Pricing Mechanism on national per-capita
-- CO2 using synthetic control. Their paper explicitly states that it cannot
-- separate the contributions of the individual policies. It therefore does
-- not identify the 2009 CPRS/Greens causal claim.
------------------------------------------------------------------------

australiaSyntheticControlCandidatePresent : Bool
australiaSyntheticControlCandidatePresent = true

kraynakTimilsinaAlberini2026 :
  CausalLiteratureCandidate March.cprs2009
kraynakTimilsinaAlberini2026 =
  causal-literature-candidate
    "doi:10.1016/j.eneco.2026.109389"
    "The effect of pricing instruments on CO2 emissions: Empirical evidence from Australia"
    "Daniel Kraynak; Govinda Timilsina; Anna Alberini"
    "Energy Economics 160 (2026), 109389"
    "synthetic control with donor pool, placebo/leave-one-out diagnostics and prediction intervals"
    "joint national effect of expanded renewable-energy incentives beginning in 2009 and the 2012-14 Carbon Pricing Mechanism on per-capita CO2 through 2018"
    syntheticControlDesign
    (Causal.GovernanceCausalEstimandDemand.causalQuestionReference
      Causal.cprsCausalEstimandDemand)
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- South Australia transition case study.
--
-- McGreevy et al. use policy-document analysis and interviews with actors in
-- the transition. This is strong same-domain historical/mechanistic context,
-- but it is not a counterfactual party-treatment design for the exact
-- long-run-Labor governance estimand.
------------------------------------------------------------------------

southAustraliaCaseStudyCandidatePresent : Bool
southAustraliaCaseStudyCandidatePresent = true

mcGreevyEtAl2021 :
  CausalLiteratureCandidate March.southAustraliaRenewables
mcGreevyEtAl2021 =
  causal-literature-candidate
    "doi:10.1016/j.enpol.2020.111940"
    "Expediting a renewable energy transition in a privatised market via public policy: The case of South Australia 2004-18"
    "Michael McGreevy; Colin MacDougall; Matt Fisher; Mark Henley; Fran Baum"
    "Energy Policy 148 (2021), 111940"
    "document analysis and interviews with key actors, interpreted through transition-management theory"
    "factors and policy initiatives associated with South Australia's renewable-electricity transition from 2004 to 2018"
    interviewDocumentCaseStudy
    (Causal.GovernanceCausalEstimandDemand.causalQuestionReference
      Causal.southAustraliaCausalEstimandDemand)
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Carbon-price attribution study.
--
-- O'Gorman / Jotzo estimate short-run effects of the 2012-14 carbon price on
-- NEM demand, supply and emissions while explicitly acknowledging fundamental
-- attribution difficulties. It is useful policy-effect evidence but targets a
-- later policy and a different causal contrast from the 2009 CPRS claim.
------------------------------------------------------------------------

carbonPriceAttributionCandidatePresent : Bool
carbonPriceAttributionCandidatePresent = true

oGormanJotzo2014 :
  CausalLiteratureCandidate March.cprs2009
oGormanJotzo2014 =
  causal-literature-candidate
    "ANU-CCEP-working-paper-1411"
    "Impact of the Carbon Price on Australia's Electricity Demand, Supply and Emissions"
    "Marianna O'Gorman; Frank Jotzo"
    "Crawford School of Public Policy CCEP Working Paper 1411"
    "before/after and quantitative attribution analysis with conservative parameters and explicit attribution caveat"
    "effects of the 2012-14 carbon price on National Electricity Market demand, supply mix and emissions"
    carbonPriceAttributionEstimate
    (Causal.GovernanceCausalEstimandDemand.causalQuestionReference
      Causal.cprsCausalEstimandDemand)
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Policy-uncertainty structural-break evidence.
--
-- This literature can support the existence of market instability associated
-- with climate-policy events; it does not identify which party caused the
-- instability or the counterfactual trajectory absent a given vote.
------------------------------------------------------------------------

policyUncertaintyCandidatePresent : Bool
policyUncertaintyCandidatePresent = true

policyUncertaintyStructuralBreakCandidate :
  CausalLiteratureCandidate March.cprs2009
policyUncertaintyStructuralBreakCandidate =
  causal-literature-candidate
    "doi-source:Energy-Economics-structural-breaks-climate-policy-uncertainty"
    "Structural breaks and electricity prices: Further evidence on the role of climate policy uncertainties in the Australian electricity market"
    "source-attributed authorship retained in publication record"
    "Energy Economics, Australian weekly wholesale electricity-price study"
    "linear and non-linear unit-root / structural-break analysis of weekly wholesale prices, 2008-2014"
    "market instability associated with Australian carbon-policy events and policy uncertainty"
    policyUncertaintyStructuralBreakStudy
    (Causal.GovernanceCausalEstimandDemand.causalQuestionReference
      Causal.cprsCausalEstimandDemand)
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Aggregate frontier: relevant literature exists, exact identification does not.
------------------------------------------------------------------------

exactPartyCausalIdentificationPaid : Bool
exactPartyCausalIdentificationPaid = false

causalLiteratureCreatesUniversalPartyRanking : Bool
causalLiteratureCreatesUniversalPartyRanking = false

data RelevantLiteratureAutomaticallyPaysIdentificationGate : Set where
data SyntheticControlPolicyMixIdentifiesCPRSPartyCause : Set where
data SACaseStudyIdentifiesLaborCounterfactual : Set where
data CarbonPriceEstimateIdentifiesCPRSBlockingEffect : Set where
data LiteratureCreatesUniversalPartyRanking : Set where

relevantLiteratureDoesNotAutomaticallyPayIdentificationGate :
  RelevantLiteratureAutomaticallyPaysIdentificationGate → ⊥
relevantLiteratureDoesNotAutomaticallyPayIdentificationGate ()

policyMixSyntheticControlDoesNotIdentifyCPRSPartyCause :
  SyntheticControlPolicyMixIdentifiesCPRSPartyCause → ⊥
policyMixSyntheticControlDoesNotIdentifyCPRSPartyCause ()

southAustraliaCaseStudyDoesNotIdentifyLaborCounterfactual :
  SACaseStudyIdentifiesLaborCounterfactual → ⊥
southAustraliaCaseStudyDoesNotIdentifyLaborCounterfactual ()

carbonPriceEstimateDoesNotIdentifyCPRSBlockingEffect :
  CarbonPriceEstimateIdentifiesCPRSBlockingEffect → ⊥
carbonPriceEstimateDoesNotIdentifyCPRSBlockingEffect ()

literatureDoesNotCreateUniversalPartyRanking :
  LiteratureCreatesUniversalPartyRanking → ⊥
literatureDoesNotCreateUniversalPartyRanking ()

record FriendlyjordiesCausalLiteratureBoundary : Set where
  constructor friendlyjordies-causal-literature-boundary
  field
    syntheticControlAcquired : Bool
    saTransitionCaseStudyAcquired : Bool
    carbonPriceAttributionStudyAcquired : Bool
    policyUncertaintyStudyAcquired : Bool
    authorshipAndMethodRetained : Bool
    exactDemandMatchPaid : Bool
    identificationGatePaid : Bool
    partySpecificCausePaid : Bool
    universalPartyRankingCreated : Bool

canonicalFriendlyjordiesCausalLiteratureBoundary :
  FriendlyjordiesCausalLiteratureBoundary
canonicalFriendlyjordiesCausalLiteratureBoundary =
  friendlyjordies-causal-literature-boundary
    true true true true true false false false false
