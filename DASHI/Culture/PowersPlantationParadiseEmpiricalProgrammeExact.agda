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
    "St Andrews identifies the local-newspaper announcement corpus; BnF identifies Affiches Americaines; Minette and enslaved-musician microhistories now carry exact issue/date/archive coordinates including 1/10 March 1787, 15 February 1764 and 13 November 1781"
    "root the cited Affiches issue images/pages directly, resolve the July 1790 date conflict, and expand event-level rows for Lise, Saint-Martin, seating/venue notices and named enslaved theatre workers"
    zero

namedPerformerStatusLeaf : EmpiricalProgrammeLeaf
namedPerformerStatusLeaf =
  empirical-programme-leaf
    "Named performer status trajectory"
    "How did documented stage participation, public naming, economic opportunity, legal status and social treatment co-vary for named performers such as Minette?"
    partialSameObjectPaid
    "peer-reviewed career/status evidence plus benefit performances, the 1784 salary contract/nonpayment receipt, the 1789 legal dispute and archival coordinates now exist for Minette"
    "inspect the underlying Affiches, Moreau, notarial, parish/civil and court records directly and construct comparable same-object trajectories for Lise and other identified performers"
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
    "business-history evidence pays commercial production; Minette's specific salary contract and named enslaved-musician theatre labour now provide performer-level economic/coercive coordinates"
    "recover theatre payrolls, directorship/ownership instruments, ticket/box prices, suppliers, benefit-night accounts and further free/enslaved labour contracts at venue/time resolution"
    (suc (suc zero))

distributionalIncidenceLeaf : EmpiricalProgrammeLeaf
distributionalIncidenceLeaf =
  empirical-programme-leaf
    "Contribution / benefit / burden / voice incidence"
    "For the same theatre actors and institutions, who contributed labour/capital/knowledge, who received income/status/pleasure, who bore coercion/risk/exclusion, and who had effective voice?"
    partialSameObjectPaid
    "Prest 2023 pays category-level enslaved spectatorship, theatre-maker ownership and enslaved contribution; the 1764 musicians and Julien 1781 further pay named-person contribution x coercive-status joins, while benefit and voice remain unresolved on those same people"
    "join named-person compensation/benefit, ownership/surplus, audience access/pricing, enslavement/coercion and governance/voice records at actor/venue/time resolution"
    (suc (suc (suc zero)))

causalMobilityLeaf : EmpiricalProgrammeLeaf
causalMobilityLeaf =
  empirical-programme-leaf
    "Causal theatre-to-status trajectory"
    "What causal effect, if any, did professional theatrical participation have on a performer's social, legal or economic standing trajectory?"
    causalIdentificationRequired
    "chronology, career, benefit-performance, contracted salary/nonpayment and legal same-object evidence establish association, mechanism surfaces and sequence only"
    "build comparable performer trajectories first; then declare population/intervention/comparator/outcome/horizon and pay an admissible identification family before estimating any causal effect"
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
    "What compensation was contracted, earned, withheld and actually settled for named performers of different legal/racial status?"
    partialSameObjectPaid
    "Minette has self-organised benefit performances plus a three-year private contract at 8000 livres per year; Prest 2019 reports Saint-Martin's 9 June 1784 will revealed that this salary had never been paid. Contract amount and nonpayment are therefore same-object paid, but estate settlement and benefit-night net proceeds are not"
    "recover Saint-Martin estate/executor settlement records, receipts or creditor/payee entries and benefit-night box-office/accounts; keep obligation, arrears, estate instruction, transfer and final settlement distinct"
    (suc zero)

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
    "requires a case-specific identification design; observed success, chronology, compensation mechanism and public naming are insufficient"

data ObservationalEvidenceIdentifiesCausalEffect : Set where

observationalEvidenceDoesNotIdentifyCausalEffect :
  ObservationalEvidenceIdentifiesCausalEffect → ⊥
observationalEvidenceDoesNotIdentifyCausalEffect ()

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
    contractedSalaryAndNonpaymentPartiallyPaid : Bool
    contractedSalaryAndNonpaymentPartiallyPaidIsTrue :
      contractedSalaryAndNonpaymentPartiallyPaid ≡ true
    categoryLevelDistributionEvidencePartiallyPaid : Bool
    categoryLevelDistributionEvidencePartiallyPaidIsTrue :
      categoryLevelDistributionEvidencePartiallyPaid ≡ true
    namedContributionBurdenJoinPartiallyPaid : Bool
    namedContributionBurdenJoinPartiallyPaidIsTrue :
      namedContributionBurdenJoinPartiallyPaid ≡ true
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
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
