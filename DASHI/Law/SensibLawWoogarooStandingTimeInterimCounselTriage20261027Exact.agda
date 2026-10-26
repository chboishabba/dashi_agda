module DASHI.Law.SensibLawWoogarooStandingTimeInterimCounselTriage20261027Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact as File
import DASHI.Law.SensibLawWoogarooLegalPriorityRoadmapExact as Legal
import DASHI.Law.SensibLawWoogarooGainLossSnowballAdapterExact as Distribution

------------------------------------------------------------------------
-- LAW P0: ACTUAL STANDING / FURNISHING / INTERIM PROCEDURAL VEHICLES.
--
-- THIS IS A COUNSEL TRIAGE, NOT A LEGAL OPINION OR A FILED APPLICATION.
-- Same-object: Springfield EPBC 2019/8575, decision noticed 15 Oct 2026.
-- Existing decision file, works/cumulative and beneficiary owners are
-- reused; original parliamentary text and the Court's own published
-- procedure retain original authorship.
--
-- Law revision correction: ADJR 29 September 2026 Compilation 134 was
-- in force on decision date; 27 August Compilation 133 is superseded.
------------------------------------------------------------------------

epbcActCurrentOctober : Source.AttributedSource
epbcActCurrentOctober = Source.mkNoDOISource
  "Parliament of Australia"
  "EPBC Act 1999 — Compilation C70, C2026C00369"
  "Original Federal Register text effective 24 August 2026"
  "24 August 2026"
  "https://www.legislation.gov.au/C2004A00485/latest"
  Source.governmentSource
  "s487(2)-(3) extends ADJR individual/organisation standing with 2-year activity and organisation objects-at-decision conditions; s475(1),(5)-(7) is a separate statutory contravention/interim injunction and interested-person test, including affected-interest alternative; s67A requires controlled-action authorisation, which the Oct decision may provide. Conditions and actual contravention remain unverified."
  Source.publicAttribution

adjrLatestSeptember : Source.AttributedSource
adjrLatestSeptember = Source.mkNoDOISource
  "Parliament of Australia"
  "Administrative Decisions (Judicial Review) Act 1977 Compilation 134, C2026C00448"
  "Original Federal Register text in force from 29 September 2026"
  "29 September 2026"
  "https://www.legislation.gov.au/C2004A01697/latest"
  Source.governmentSource
  "s3(4) interest affected, s3(6) deemed furnishing by paid post; ss5,11(1)(c),(3)-(5),13(1),(5),15(1)-(2),16 review reasons, applicant-specific furnishing/time, no automatic stay, available discretionary relief. s13 eligibility and notice are distinct from an any-person s135A report request; counsel must check excluded decisions, proper Court route and potential extensions."
  Source.publicAttribution

courtRulesJune2026 : Source.AttributedSource
courtRulesJune2026 = Source.mkNoDOISource
  "Federal Court of Australia / Federal Register of Legislation"
  "Federal Court Rules 2011 — 11 June 2026 compilation"
  "Original Federal Court Rules text"
  "11 June 2026"
  "https://www.legislation.gov.au/F2011L01551/2026-06-11/2026-06-11/text/original/epub/OEBPS/document_1/document_1.html"
  Source.governmentSource
  "r31.01 ADJR Form 66, r31.02 extension Form 67 with affidavit and draft application, r17.01 Form 35 for existing matter, r7.01(2) pre-commencement urgent Form 12/affidavit; filing and service obligations remain applicant-specific."
  Source.publicAttribution

courtUrgentGuide : Source.AttributedSource
courtUrgentGuide = Source.mkNoDOISource
  "Federal Court of Australia"
  "Urgent (Duty) Matters: how to apply"
  "Original Court administrative practice and forms"
  "October 2026 access"
  "https://www.fedcourt.gov.au/contact/urgent-duty-matters"
  Source.governmentSource
  "Court requires Certificate of Urgency/GPN-DUTY, identifies Form 12 pre-commencement, Form 35 post-commencement and duty contact procedure, including after-hours. The need for urgent listing cannot be inferred simply from past ecological risk."
  Source.publicAttribution

courtUndertakingGuide : Source.AttributedSource
courtUndertakingGuide = Source.mkNoDOISource
  "Federal Court of Australia"
  "GPN-UNDR: Usual Undertaking as to Damages"
  "Original 25 October 2016 Court practice note"
  "25 October 2016"
  "https://www.fedcourt.gov.au/law-and-practice/practice-documents/practice-notes/gpn-undr"
  Source.governmentSource
  "Court almost always expects interlocutory applicant to give undertaking as to damages; inability/exception and risk to group/public interest need specific counsel and court consideration."
  Source.publicAttribution

edoIntake : Source.AttributedSource
edoIntake = Source.mkNoDOISource
  "Environmental Defenders Office"
  "Apply for free legal advice"
  "Original nonprofit practitioner legal intake"
  "October 2026 access"
  "https://www.edo.org.au/free-legal-advice/"
  Source.practitionerSource
  "Environmental law advice application requires urgency stated; assesses intake/conflicts and availability, does not promise to represent applicant or file. Separate from court registry procedural access."
  Source.publicAttribution

data StandingApplicant : Set where
  conservationIndividual : StandingApplicant
  conservationOrganisation : StandingApplicant
  affectedNeighbourOrInterestedPerson : StandingApplicant

data ProtectionRoute : Set where
  adjrSection5Review : ProtectionRoute
  judiciarySection39BOriginalJurisdiction : ProtectionRoute
  adjrSection15Stay : ProtectionRoute
  epbcSection475ContraventionInjunction : ProtectionRoute
  courtRule701ProspectiveEmergency : ProtectionRoute

data CaseStatus : Set where
  routeAvailableInLaw : CaseStatus
  caseSpecificProofOpen : CaseStatus
  courtOrderNotSought : CaseStatus

record LitigationGate : Set where
  constructor litigation-gate
  field
    route : ProtectionRoute
    authority : Source.AttributedSource
    status : CaseStatus
    eligibleApplicantOrTrigger : String
    exactlyMissing : String
    resultObtained : Bool
    failClosed : resultObtained ≡ false
open LitigationGate public

individualStanding : LitigationGate
individualStanding = litigation-gate adjrSection5Review epbcActCurrentOctober
  caseSpecificProofOpen
  "Australian citizen/ordinarily resident person with qualifying series of conservation/research/protection activities within 15 Oct 2024–15 Oct 2026; EPBC s487(2). Alternatively ADJR s3(4) affected personal interests."
  "Identified litigant, citizen/residence proof, date-by-date two-year environmental activities and sworn source/provenance."
  false refl

organisationStanding : LitigationGate
organisationStanding = litigation-gate adjrSection5Review epbcActCurrentOctober
  caseSpecificProofOpen
  "Australian-incorporated/established organisation or association, series of environmental activities within preceding two years, and environmental objects AT 15 Oct decision; s487(3)."
  "Original constitution at 15 Oct 2026, Australian establishment, board authorisation, preserved dated activity documents and correct legal applicant."
  false refl

independentAffectedInterest : LitigationGate
independentAffectedInterest = litigation-gate adjrSection5Review adjrLatestSeptember
  caseSpecificProofOpen
  "ADJR s3(4) adversely affected interests may provide ordinary standing beyond s487 conservation-activity path."
  "Named applicant, concrete connection and impacts, evidence of why interest is more than general political concern."
  false refl

section39BAlternative : LitigationGate
section39BAlternative = litigation-gate judiciarySection39BOriginalJurisdiction courtRulesJune2026
  caseSpecificProofOpen
  "Federal Court Rules 31.01(3) permits joinder of same-subject section 39B Judiciary Act claim with ADJR; availability/reviewability and relief require counsel analysis."
  "Exact ground, respondent/delegate identity, remedial jurisdiction, limitations and whether ADJR is excluded."
  false refl

furnishingClock : LitigationGate
furnishingClock = litigation-gate adjrSection5Review adjrLatestSeptember
  caseSpecificProofOpen
  "ADJR s11(1)(c),(3) decision/qualified reasons furnished to particular applicant, not necessarily date online. Section 3(6) includes deemed furnishing on prepaid post in certain circumstances."
  "Each applicant's original terms/reasons, receipt or service log, postal record, eligible timely s13 request and court extension facts."
  false refl

stayAfterFiling : LitigationGate
stayAfterFiling = litigation-gate adjrSection15Stay adjrLatestSeptember
  caseSpecificProofOpen
  "Filing an ADJR s5 review does not stay approval. Court may suspend decision or stay proceedings on an application or own motion under s15."
  "Actually filed or intended proceeding, applicant and respondent, proposed order, serious legal issue, urgency, harm/cost evidence, counsel."
  false refl

epbcContravention : LitigationGate
epbcContravention = litigation-gate epbcSection475ContraventionInjunction epbcActCurrentOctober
  caseSpecificProofOpen
  "EPBC s475(1),(5) can restrain actual/proposed contravention, with interested person under s475(6)/(7): affected interests OR environmental activities; distinct from s487 standing."
  "Exact threatened works polygon, current signed conditions, on-ground commencement, breach of term or works outside approved action; otherwise authorised clearing is NOT automatically unlawful."
  false refl

beforeOriginating : LitigationGate
beforeOriginating = litigation-gate courtRule701ProspectiveEmergency courtUrgentGuide
  caseSpecificProofOpen
  "Urgent prospective applicant r7.01/Form12 with affidavit, Certificate of Urgency and Court procedural notice, assessed case by case."
  "Dated threat of irreversible harm, witnessed activity, draft narrow orders and relevant corporate approval holder to bind; costs/undertaking advice."
  false refl

undertakingRisk : LitigationGate
undertakingRisk = litigation-gate courtRule701ProspectiveEmergency courtUndertakingGuide
  caseSpecificProofOpen
  "Court generally expects usual undertaking as to damages, potentially material exposure for conservation applicant."
  "Counsel advice on delay-cost evidence, undertaking ability, adverse costs and any possible exception; no universal public-interest waiver."
  false refl

triageGates : List LitigationGate
triageGates =
  individualStanding ∷ organisationStanding ∷ independentAffectedInterest ∷
  section39BAlternative ∷ furnishingClock ∷ stayAfterFiling ∷
  epbcContravention ∷ beforeOriginating ∷ undertakingRisk ∷ []

-- Existing source and case consumers are genuinely reused. Nothing in their
-- existence turns a candidate applicant into a qualified litigant.
originalDocumentRecommendationGate : File.DecisionFileReceipt
originalDocumentRecommendationGate = File.section95CRecommendation

preApprovalCumulativeRecord : String
preApprovalCumulativeRecord =
  "Prior Cumulative owner exists, but full final PD, Ministerial response and same-parcel Item 4.6(c) scientific material remain to be checked"

originalLegalPriority : Legal.LegalPriorityCoordinate
originalLegalPriority = Legal.federal8575Priority

originalEcologicalBurden : Distribution.DistributionResidual
originalEcologicalBurden = Distribution.whoBearsEcologicalLoss

data ConservationIdentityAloneProvesSection487 : Set where
data PortalPublicationProvesParticularApplicantFurnishing : Set where
data Section135AReportRequestTollsADJRTime : Set where
data Section475PermitsStoppingAnyApprovedProject : Set where
data KoalaHabitatAloneProvesBreachOrUrgency : Set where
data FiledADJRCaseAutomaticallyStaysDecision : Set where
data InterlocutoryReliefGuaranteesCostIndemnityWaiver : Set where
data PoliticalLobbyingAloneEstablishesReviewGround : Set where
data CourtRegistryCanGiveIndividualLegalAdvice : Set where
data ThisSourceWrittenOwnerIsCourtFinding : Set where

identityNotStanding : ConservationIdentityAloneProvesSection487 → ⊥
identityNotStanding ()

onlineNoticeNotFurnishing : PortalPublicationProvesParticularApplicantFurnishing → ⊥
onlineNoticeNotFurnishing ()

requestNotToll : Section135AReportRequestTollsADJRTime → ⊥
requestNotToll ()

conditionalApprovalNotAutomaticallyContravention :
  Section475PermitsStoppingAnyApprovedProject → ⊥
conditionalApprovalNotAutomaticallyContravention ()

habitatNotBreach : KoalaHabitatAloneProvesBreachOrUrgency → ⊥
habitatNotBreach ()

filingDoesNotAutomaticallyStay : FiledADJRCaseAutomaticallyStaysDecision → ⊥
filingDoesNotAutomaticallyStay ()

publicInterestNotCostsExemption :
  InterlocutoryReliefGuaranteesCostIndemnityWaiver → ⊥
publicInterestNotCostsExemption ()

politicsNotGround : PoliticalLobbyingAloneEstablishesReviewGround → ⊥
politicsNotGround ()

registryNotLegalCounsel : CourtRegistryCanGiveIndividualLegalAdvice → ⊥
registryNotLegalCounsel ()

sourceCodeNotCourtFinding : ThisSourceWrittenOwnerIsCourtFinding → ⊥
sourceCodeNotCourtFinding ()
