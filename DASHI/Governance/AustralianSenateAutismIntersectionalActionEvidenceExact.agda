module DASHI.Governance.AustralianSenateAutismIntersectionalActionEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Governance.AustralianSenateAutismInquiryExact as Inquiry
import DASHI.Governance.AustralianSenateAutismIntersectionalityExact as Intersectional
import DASHI.Governance.RecognitionDistributionRepresentationAxesExact as Fraser

------------------------------------------------------------------------
-- RECOMMENDATION 18 -> DOWNSTREAM ACTION-EVIDENCE SNOWBALL
--
-- This owner pays only source-bound participation/action coordinates recovered
-- from DSS development and First Action Plan materials. Consultation,
-- representation, funded action, service access and measured outcome remain
-- distinct. The committee's finite cohort list remains non-exhaustive.
------------------------------------------------------------------------

dssStrategyDevelopment : Source.AttributedSource
dssStrategyDevelopment = Source.mkNoDOISource
  "Australian Government Department of Social Services"
  "Development of the National Autism Strategy"
  "Department of Social Services"
  "2023–2024"
  "https://www.dss.gov.au/national-autism-strategy/development-national-autism-strategy"
  Source.governmentSource
  "Primary administrative source for co-design/consultation process and targeted focus-group participation; participation does not itself prove service distribution or outcomes."
  Source.publicAttribution

dssFirstActionPlan : Source.AttributedSource
dssFirstActionPlan = Source.mkNoDOISource
  "Australian Government Department of Social Services"
  "National Autism Strategy First Action Plan 2025–2026"
  "Department of Social Services"
  "2025"
  "https://www.dss.gov.au/national-autism-strategy/resource/national-autism-strategy-first-action-plan-2025-2026"
  Source.governmentSource
  "Primary downstream action-plan carrier. Specific listed actions may pay bounded action coordinates but do not automatically establish implementation completion, equitable access or outcomes."
  Source.publicAttribution

dssStrategyRelease : Source.AttributedSource
dssStrategyRelease = Source.mkNoDOISource
  "Australian Government Department of Social Services Ministers"
  "Release of the first National Autism Strategy"
  "Department of Social Services Ministers"
  "2025"
  "https://ministers.dss.gov.au/media-releases/17301"
  Source.governmentSource
  "Government release recording funded First Action Plan measures, including peer support, evaluation, employment, diagnosis resources, knowledge translation and prevalence work; announcement does not equal completed delivery."
  Source.publicAttribution

intersectionalActionSources : List Source.AttributedSource
intersectionalActionSources =
  dssStrategyDevelopment ∷
  dssFirstActionPlan ∷
  dssStrategyRelease ∷
  []

intersectionalActionAtlas : Source.AttributedSourceAtlas
intersectionalActionAtlas = Source.mkSourceAtlas
  "National Autism Strategy intersectional action evidence atlas"
  "DASHI.Governance.AustralianSenateAutismIntersectionalActionEvidenceExact"
  intersectionalActionSources
  "Downstream co-design and action evidence relevant to Recommendation 18, with representation/distribution/outcome boundaries retained."

------------------------------------------------------------------------
-- Recommendation-18 cohort coordinates. These are source-local query labels,
-- not a new universal ontology of autistic identity.
------------------------------------------------------------------------

data R18CohortCoordinate : Set where
  autisticAdults : R18CohortCoordinate
  womenGirlsGenderDiverse : R18CohortCoordinate
  lowerSocioeconomic : R18CohortCoordinate
  regionalRemote : R18CohortCoordinate
  firstNations : R18CohortCoordinate
  caldCarm : R18CohortCoordinate
  lgbtqiaNonHeterosexual : R18CohortCoordinate
  complexHighSupportNeeds : R18CohortCoordinate
  additionalAffectedConstituency : String → R18CohortCoordinate

data EvidenceSurface : Set where
  targetedConsultationSurface : EvidenceSurface
  actionPlanDesignSurface : EvidenceSurface
  fundedProgramSurface : EvidenceSurface
  serviceAccessSurface : EvidenceSurface
  measuredOutcomeSurface : EvidenceSurface

data PaymentState : Set where
  sourcePaid : PaymentState
  partialActionPaid : PaymentState
  paymentOpen : PaymentState

record CohortEvidence : Set where
  constructor cohort-evidence
  field
    cohort : R18CohortCoordinate
    surface : EvidenceSurface
    source : Source.AttributedSource
    exactLocator : String
    boundedStatement : String
    payment : PaymentState
    paysWholeRecommendation18 : Bool
    paysWholeRecommendation18IsFalse : paysWholeRecommendation18 ≡ false
    paysMeasuredOutcome : Bool
    paysMeasuredOutcomeIsFalse : paysMeasuredOutcome ≡ false

open CohortEvidence public

------------------------------------------------------------------------
-- Participation / representation evidence from the co-design process.
------------------------------------------------------------------------

firstNationsConsultation : CohortEvidence
firstNationsConsultation = cohort-evidence
  firstNations targetedConsultationSurface dssStrategyDevelopment
  "Phase 2 — targeted focus groups"
  "DSS records a targeted focus group with Autistic First Nations people during development of the Strategy."
  sourcePaid false refl false refl

caldConsultation : CohortEvidence
caldConsultation = cohort-evidence
  caldCarm targetedConsultationSurface dssStrategyDevelopment
  "Phase 2 — targeted focus groups"
  "DSS records a targeted focus group with Autistic people from culturally and linguistically diverse backgrounds."
  sourcePaid false refl false refl

lgbtqiaConsultation : CohortEvidence
lgbtqiaConsultation = cohort-evidence
  lgbtqiaNonHeterosexual targetedConsultationSurface dssStrategyDevelopment
  "Phase 2 — targeted focus groups"
  "DSS records a targeted focus group with Autistic people from the LGBTQIA+ community."
  sourcePaid false refl false refl

womenGenderConsultation : CohortEvidence
womenGenderConsultation = cohort-evidence
  womenGirlsGenderDiverse targetedConsultationSurface dssStrategyDevelopment
  "Phase 2 — targeted focus groups"
  "DSS records a targeted focus group with Autistic women, girls and non-binary people."
  sourcePaid false refl false refl

complexNeedsConsultation : CohortEvidence
complexNeedsConsultation = cohort-evidence
  complexHighSupportNeeds targetedConsultationSurface dssStrategyDevelopment
  "Phase 2 — targeted focus groups"
  "DSS records targeted participation by families and carers including people with very high support and dependency needs."
  sourcePaid false refl false refl

------------------------------------------------------------------------
-- Action-level evidence. The First Action Plan evaluation explicitly considers
-- intersectional disadvantage and geography. The peer-support action is
-- described as Autistic-led, culturally sensitive and tailored to priority
-- cohorts, including First Nations and CALD/CARM communities.
------------------------------------------------------------------------

firstNationsPeerSupportAction : CohortEvidence
firstNationsPeerSupportAction = cohort-evidence
  firstNations fundedProgramSurface dssFirstActionPlan
  "Commitment 2 / peer support action"
  "The First Action Plan describes Autistic-led peer support tailored to priority cohorts and explicitly includes First Nations communities among underrepresented groups for increased access to resources, services and advocacy."
  partialActionPaid false refl false refl

caldPeerSupportAction : CohortEvidence
caldPeerSupportAction = cohort-evidence
  caldCarm fundedProgramSurface dssFirstActionPlan
  "Commitment 2 / peer support action"
  "The First Action Plan describes culturally sensitive Autistic-led peer support and explicitly includes CALD/CARM communities among underrepresented groups for increased access to resources, services and advocacy."
  partialActionPaid false refl false refl

regionalGeographyEvaluation : CohortEvidence
regionalGeographyEvaluation = cohort-evidence
  regionalRemote actionPlanDesignSurface dssFirstActionPlan
  "Commitment 2 / peer-support model evaluation"
  "The First Action Plan requires evaluation of geographical factors in peer-support models; this is not equivalent to the regional service-access actions recommended by the Senate."
  partialActionPaid false refl false refl

intersectionalDisadvantageEvaluation : CohortEvidence
intersectionalDisadvantageEvaluation = cohort-evidence
  (additionalAffectedConstituency "people facing intersectional disadvantage")
  actionPlanDesignSurface dssFirstActionPlan
  "Commitment 2 / peer-support model evaluation"
  "The First Action Plan requires evaluation of whether peer-support models consider the needs of Autistic people facing intersectional disadvantage."
  partialActionPaid false refl false refl

------------------------------------------------------------------------
-- Existing recognition/distribution/representation geometry applied to these
-- sources. Consultation can pay a bounded representation observation without
-- paying material distribution; a funded program can pay an action coordinate
-- without proving equitable access or longitudinal outcome.
------------------------------------------------------------------------

targetedConsultationPaysOutcome : Bool
targetedConsultationPaysOutcome = false

targetedConsultationPaysMaterialDistribution : Bool
targetedConsultationPaysMaterialDistribution = false

peerSupportActionPaysAllRecommendation18 : Bool
peerSupportActionPaysAllRecommendation18 = false

someCohortSpecificActionEvidencePaid : Bool
someCohortSpecificActionEvidencePaid = true

recognitionStillSeparateFromDistribution :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Fraser.recognition Fraser.distribution →
  ⊥
recognitionStillSeparateFromDistribution = Fraser.recognitionCannotRecoverDistribution

------------------------------------------------------------------------
-- Explicit unpaid high-alpha coordinates.
------------------------------------------------------------------------

lowerSocioeconomicActionPaymentOpen : Bool
lowerSocioeconomicActionPaymentOpen = true

regionalRemoteServiceAccessPaymentOpen : Bool
regionalRemoteServiceAccessPaymentOpen = true

complexNeedsIntegratedSupportPaymentOpen : Bool
complexNeedsIntegratedSupportPaymentOpen = true

autisticAdultsServiceActionPaymentOpen : Bool
autisticAdultsServiceActionPaymentOpen = true

womenGirlsServiceActionPaymentOpen : Bool
womenGirlsServiceActionPaymentOpen = true

lgbtqiaServiceActionPaymentOpen : Bool
lgbtqiaServiceActionPaymentOpen = true

------------------------------------------------------------------------
-- Ordered intersectional snowball after this tranche.
------------------------------------------------------------------------

data ActionSnowballLeaf : Set where
  consultationParticipationLeaf : ActionSnowballLeaf
  actionDesignLeaf : ActionSnowballLeaf
  fundedCohortProgramLeaf : ActionSnowballLeaf
  equitableServiceAccessLeaf : ActionSnowballLeaf
  longitudinalOutcomeLeaf : ActionSnowballLeaf

currentActionPaymentFrontier : ActionSnowballLeaf
currentActionPaymentFrontier = equitableServiceAccessLeaf

highestAlphaActionResidual : String
highestAlphaActionResidual =
  "Acquire literal service-access/implementation evidence for still-open Recommendation 18 cohorts, prioritising lower-socioeconomic, regional/remote and complex-needs coordinates; distinguish representation from distribution and one funded peer-support action from whole-of-life service sufficiency."

record IntersectionalActionBoundary : Set where
  constructor intersectional-action-boundary
  field
    consultationEqualsOutcome : Bool
    consultationEqualsDistribution : Bool
    oneProgramEqualsWholeRecommendation : Bool
    cohortListExhaustive : Bool
    someActionEvidenceNowPaid : Bool

canonicalIntersectionalActionBoundary : IntersectionalActionBoundary
canonicalIntersectionalActionBoundary =
  intersectional-action-boundary false false false false true
