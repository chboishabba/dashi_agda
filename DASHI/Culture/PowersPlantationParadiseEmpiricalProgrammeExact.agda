module DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.BenefitBurdenExternalityDistributionExact as Distribution
import DASHI.Core.ResponsibilityBurdenNonfactorabilityExact as Responsibility
import DASHI.Biology.CausalEffectEstimandExact as Causal
import DASHI.Culture.PowersPlantationParadiseSourceAtlasExact as Atlas
import DASHI.Culture.PowersPlantationParadiseMinetteMicrohistoryExact as Minette
import DASHI.Culture.PowersPlantationParadiseEnslavedDistributionEvidenceExact as EnslavedEvidence

------------------------------------------------------------------------
-- POWERS EMPIRICAL PROGRAMME
------------------------------------------------------------------------

data EmpiricalEvidenceClass : Set where
  peerReviewedSecondaryEvidence : EmpiricalEvidenceClass
  archivalCatalogueEvidence : EmpiricalEvidenceClass
  institutionalResearchDatabaseEvidence : EmpiricalEvidenceClass
  archivalLocatorEvidence : EmpiricalEvidenceClass
  scholarlyBusinessHistoryEvidence : EmpiricalEvidenceClass

record SameObjectEmpiricalReceipt : Set where
  constructor same-object-empirical-receipt
  field
    subjectReference : String
    venueReference : String
    timeReference : String
    claimReference : String
    source : Source.AttributedSource
    evidenceClass : EmpiricalEvidenceClass
    promotesCausalEffect : Bool
    promotesCausalEffectIsFalse : promotesCausalEffect ≡ false
    promotesPopulationLaw : Bool
    promotesPopulationLawIsFalse : promotesPopulationLaw ≡ false

open SameObjectEmpiricalReceipt public

------------------------------------------------------------------------
-- 1. Named performer / status same-object evidence.
------------------------------------------------------------------------

minetteCareerStatusReceipt : SameObjectEmpiricalReceipt
minetteCareerStatusReceipt =
  same-object-empirical-receipt
    "Minette, named performer of colour in Saint-Domingue theatre history"
    "Port-au-Prince public theatre and documented Saint-Domingue performance circuit"
    "late-1780 concert appearance; retrospective 13 February 1781 theatre debut; full theatrical benefit performance 6 March 1781; career evidence through the 1780s"
    "Prest's peer-reviewed reconstruction documents Minette in solo stage roles and treats her theatre success as permitting some social mobility while not insulating her from racial prejudice; finer chronology is retained in the Minette microhistory owner rather than collapsing distinct public-appearance predicates"
    Atlas.prestRacialScaleSource
    peerReviewedSecondaryEvidence
    false refl
    false refl

minetteMicrohistoryBoundary : Minette.MinetteMicrohistoryBoundary
minetteMicrohistoryBoundary = Minette.canonicalMinetteMicrohistoryBoundary

------------------------------------------------------------------------
-- 2. Racialised venue geometry.
------------------------------------------------------------------------

portAuPrinceSeatingGeometryReceipt : SameObjectEmpiricalReceipt
portAuPrinceSeatingGeometryReceipt =
  same-object-empirical-receipt
    "free people of colour attending the Port-au-Prince theatre"
    "Port-au-Prince theatre"
    "late eighteenth-century Saint-Domingue; Prest's reconstruction of the colonial seating regime"
    "Prest reports a segregated seating allocation for free people of colour in a second-tier box sector, providing same-object evidence that admission and spatial location were distinct coordinates"
    Atlas.prestRacialScaleSource
    peerReviewedSecondaryEvidence
    false refl
    false refl

portAuPrinceFloorplanReceipt : SameObjectEmpiricalReceipt
portAuPrinceFloorplanReceipt =
  same-object-empirical-receipt
    "racialised audience classes represented in the theatre-plan legend"
    "Theatre de Port-au-Prince"
    "1782"
    "the Laméca institutional dossier reproduces a Port-au-Prince theatre plan whose legend includes a second row of boxes for people of colour and supplies archival locator ANOM FM F3 296 E 75; this receipt records the located reproduction, not inspection of the ANOM original"
    Atlas.lamecaSaintDomingueOperaSource
    archivalLocatorEvidence
    false refl
    false refl

------------------------------------------------------------------------
-- 3. Venue economy / institutional production surface.
------------------------------------------------------------------------

portAuPrinceBusinessReceipt : SameObjectEmpiricalReceipt
portAuPrinceBusinessReceipt =
  same-object-empirical-receipt
    "Port-au-Prince theatre institution, troupe and commercial operation"
    "Port-au-Prince theatre"
    "late 1770s through 1780s"
    "Clay's theatre-business history supplies a same-object institutional-production surface: colonial playhouse capacity, professional staffing, commercial pressure and participation by free people of colour are historically observable coordinates; this receipt does not infer wages, ownership shares, realised profits, surplus incidence or burden distribution"
    Atlas.clayStagestruckSource
    scholarlyBusinessHistoryEvidence
    false refl
    false refl

------------------------------------------------------------------------
-- 4. Primary-corpus acquisition route.
------------------------------------------------------------------------

theatreCorpusProvenanceReceipt : SameObjectEmpiricalReceipt
theatreCorpusProvenanceReceipt =
  same-object-empirical-receipt
    "Saint-Domingue public theatre announcements and named performance events"
    "multiple Saint-Domingue theatre towns including Port-au-Prince and Cap-Francais"
    "1764-1791"
    "the St Andrews Theatre in Saint-Domingue project identifies local newspaper announcements as the principal surviving systematic performance source and exposes a database-oriented route for event, venue, repertoire and participant recovery; the BnF Affiches Americaines catalogue independently pays corpus identity but not any uninspected issue claim"
    Atlas.theatreSaintDomingueProjectSource
    institutionalResearchDatabaseEvidence
    false refl
    false refl

------------------------------------------------------------------------
-- 5. Reuse the generic distribution and responsibility boundaries.
------------------------------------------------------------------------

benefitBurdenBoundary : Distribution.BenefitBurdenExternalityBoundary
benefitBurdenBoundary = Distribution.canonicalBenefitBurdenExternalityBoundary

responsibilityBurdenBoundary : Responsibility.ResponsibilityBurdenBoundary
responsibilityBurdenBoundary = Responsibility.canonicalResponsibilityBurdenBoundary

causalEstimandBoundary : Causal.CausalEffectEstimandBoundary
causalEstimandBoundary = Causal.canonicalCausalEffectEstimandBoundary

enslavedDistributionBoundary :
  EnslavedEvidence.PowersEnslavedDistributionEvidenceBoundary
enslavedDistributionBoundary =
  EnslavedEvidence.canonicalPowersEnslavedDistributionEvidenceBoundary

------------------------------------------------------------------------
-- 6. Explicit empirical programme leaves.
------------------------------------------------------------------------

data EmpiricalProgrammeStatus : Set where
  sameObjectPaid : EmpiricalProgrammeStatus
  partialSameObjectPaid : EmpiricalProgrammeStatus
  sourceSurfaceLocated : EmpiricalProgrammeStatus
  unpaidSameObject : EmpiricalProgrammeStatus
  causalIdentificationRequired : EmpiricalProgrammeStatus

record EmpiricalProgrammeLeaf : Set where
  constructor empirical-programme-leaf
  field
    leafName : String
    question : String
    status : EmpiricalProgrammeStatus
    currentEvidence : String
    nextSameObjectAcquisition : String
    priority : Nat

open EmpiricalProgrammeLeaf public

primaryCorpusSaturationLeaf : EmpiricalProgrammeLeaf
primaryCorpusSaturationLeaf =
  empirical-programme-leaf
    "Primary performance-corpus saturation"
    "Which exact performance events, venues, participants, advertisements and status terms can be recovered from surviving Saint-Domingue announcements?"
    sourceSurfaceLocated
    "St Andrews identifies the local-newspaper announcement corpus and exposes a performance database route; BnF identifies Affiches Americaines as a primary archival corpus; the Minette microhistory now carries several issue/date/archive coordinates"
    "extract and root exact event-level rows against issue/date/page or archival image coordinates, beginning with the benefit performances, Lise, Saint-Martin, Port-au-Prince seating/venue notices and named performers of colour"
    zero

namedPerformerStatusLeaf : EmpiricalProgrammeLeaf
namedPerformerStatusLeaf =
  empirical-programme-leaf
    "Named performer status trajectory"
    "How did documented stage participation, public naming, economic opportunity, legal status and social treatment co-vary for named performers such as Minette?"
    partialSameObjectPaid
    "peer-reviewed career/status evidence plus exact benefit-performance, legal-dispute and archival-coordinate surfaces now exist for Minette"
    "inspect the underlying Affiches, Moreau, ANOM parish/civil and court records directly and construct comparable same-object trajectories for Lise and other identified performers"
    (suc zero)

venueSeatingAccessLeaf : EmpiricalProgrammeLeaf
venueSeatingAccessLeaf =
  empirical-programme-leaf
    "Venue seating and access geometry"
    "Who could enter, where could they sit, and which racial/legal classes were spatially separated within the same theatre?"
    sameObjectPaid
    "peer-reviewed seating reconstruction plus a located 1782 Port-au-Prince theatre plan with an explicit people-of-colour box sector"
    "inspect the ANOM original and recover additional venue plans, ordinances, seat-price schedules and local notices to distinguish architecture, policy and practice"
    (suc zero)

venueEconomyLeaf : EmpiricalProgrammeLeaf
venueEconomyLeaf =
  empirical-programme-leaf
    "Venue economy and production relations"
    "Who staffed, financed, directed, owned, supplied and profited from the colonial theatre, and on what terms?"
    partialSameObjectPaid
    "business-history evidence pays a commercial theatre institution and professional staffing surface"
    "recover payrolls, performer contracts, directorship/ownership instruments, creditor records, ticket/box prices, supplier accounts and any forced or enslaved labour inputs"
    (suc (suc zero))

distributionalIncidenceLeaf : EmpiricalProgrammeLeaf
distributionalIncidenceLeaf =
  empirical-programme-leaf
    "Contribution / benefit / burden / voice incidence"
    "For the same theatre actors and institutions, who contributed labour/capital/knowledge, who received income/status/pleasure, who bore coercion/risk/exclusion, and who had effective voice?"
    partialSameObjectPaid
    "Prest 2023 pays category-level same-domain evidence for enslaved spectatorship, theatre-maker slave ownership and concealed enslaved participation in theatre-making; generic DASHI distribution geometry still blocks promotion from those categories to complete actor-level incidence"
    "join exact named-person labour/contribution, ownership/surplus, audience access/pricing, enslavement/coercion and governance/voice records at actor/venue/time resolution"
    (suc (suc (suc zero)))

causalMobilityLeaf : EmpiricalProgrammeLeaf
causalMobilityLeaf =
  empirical-programme-leaf
    "Causal theatre-to-status trajectory"
    "What causal effect, if any, did professional theatrical participation have on a performer's social, legal or economic standing trajectory?"
    causalIdentificationRequired
    "chronology, career, benefit-performance and legal same-object evidence establish association, mechanism surfaces and sequence only"
    "declare population/intervention/comparator/outcome/horizon, select an admissible identification family, and obtain same-object comparison evidence before estimating any causal effect"
    (suc (suc (suc (suc zero))))

legalStatusSeatingRuleLeaf : EmpiricalProgrammeLeaf
legalStatusSeatingRuleLeaf =
  empirical-programme-leaf
    "Legal-status / seating-rule source recovery"
    "Which colonial legal or administrative instruments governed theatre admission and racialised seating, and how did those rules differ from observed practice?"
    sourceSurfaceLocated
    "peer-reviewed and plan evidence pay observed/represented segregation but not the complete rule-producing legal instrument chain"
    "recover ordinances, police/theatre regulations, municipal or colonial council records and enforcement notices with exact venue/date applicability"
    (suc (suc zero))

compensationPaymentLeaf : EmpiricalProgrammeLeaf
compensationPaymentLeaf =
  empirical-programme-leaf
    "Performer compensation and payment completion"
    "What compensation was promised, earned and actually paid to named performers of different legal/racial status?"
    partialSameObjectPaid
    "Minette is documented in self-organised benefit performances, establishing a performer-specific revenue mechanism; this does not pay contractual entitlement, gross receipts, expenses, net proceeds or settlement"
    "recover contracts, benefit-night account/box-office receipts, payroll/account-book fragments, litigation and creditor records; keep benefit performance, promised amount, net proceeds and actual settlement distinct"
    (suc (suc zero))

------------------------------------------------------------------------
-- 7. Causal question is typed as a demand, not an inferred effect.
------------------------------------------------------------------------

record PowersCausalQuestionDemand : Set where
  constructor powers-causal-question-demand
  field
    kind : Causal.CausalEstimandKind
    populationReference : String
    interventionReference : String
    comparatorReference : String
    outcomeReference : String
    timeReference : String
    identificationRequirement : String

open PowersCausalQuestionDemand public

theatreParticipationMobilityCausalDemand : PowersCausalQuestionDemand
theatreParticipationMobilityCausalDemand =
  powers-causal-question-demand
    Causal.trajectoryEffect
    "named performers in a specified Saint-Domingue venue/career cohort"
    "documented professional theatrical participation/exposure"
    "an explicitly justified counterfactual or matched lower-exposure trajectory"
    "social, legal and economic standing over time"
    "declared 1780s career horizon with source-matched observation points"
    "requires a case-specific identification design; observed success, chronology, benefit mechanism and public naming are insufficient"

data ObservationalEvidenceIdentifiesCausalEffect : Set where

observationalEvidenceDoesNotIdentifyCausalEffect :
  ObservationalEvidenceIdentifiesCausalEffect → ⊥
observationalEvidenceDoesNotIdentifyCausalEffect ()

------------------------------------------------------------------------
-- 8. Terminal empirical-programme boundary.
------------------------------------------------------------------------

record PowersEmpiricalProgrammeBoundary : Set where
  constructor powers-empirical-programme-boundary
  field
    namedPerformerSameObjectEvidencePaid : Bool
    namedPerformerSameObjectEvidencePaidIsTrue :
      namedPerformerSameObjectEvidencePaid ≡ true
    segregatedSeatingSameObjectEvidencePaid : Bool
    segregatedSeatingSameObjectEvidencePaidIsTrue :
      segregatedSeatingSameObjectEvidencePaid ≡ true
    venueBusinessSameObjectEvidencePartiallyPaid : Bool
    venueBusinessSameObjectEvidencePartiallyPaidIsTrue :
      venueBusinessSameObjectEvidencePartiallyPaid ≡ true
    performerBenefitMechanismPartiallyPaid : Bool
    performerBenefitMechanismPartiallyPaidIsTrue :
      performerBenefitMechanismPartiallyPaid ≡ true
    categoryLevelDistributionEvidencePartiallyPaid : Bool
    categoryLevelDistributionEvidencePartiallyPaidIsTrue :
      categoryLevelDistributionEvidencePartiallyPaid ≡ true
    primaryCorpusAcquisitionRouteIdentified : Bool
    primaryCorpusAcquisitionRouteIdentifiedIsTrue :
      primaryCorpusAcquisitionRouteIdentified ≡ true
    contributionBenefitBurdenVoiceDistributionPaid : Bool
    contributionBenefitBurdenVoiceDistributionPaidIsFalse :
      contributionBenefitBurdenVoiceDistributionPaid ≡ false
    observationalEvidenceIdentifiesCausalEffect : Bool
    observationalEvidenceIdentifiesCausalEffectIsFalse :
      observationalEvidenceIdentifiesCausalEffect ≡ false
    archivalLocatorEqualsArchiveInspection : Bool
    archivalLocatorEqualsArchiveInspectionIsFalse :
      archivalLocatorEqualsArchiveInspection ≡ false
    scholarlySecondaryEqualsPrimaryRecord : Bool
    scholarlySecondaryEqualsPrimaryRecordIsFalse :
      scholarlySecondaryEqualsPrimaryRecord ≡ false

canonicalPowersEmpiricalProgrammeBoundary : PowersEmpiricalProgrammeBoundary
canonicalPowersEmpiricalProgrammeBoundary =
  powers-empirical-programme-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
