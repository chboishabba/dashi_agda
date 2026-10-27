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
import DASHI.Law.SensibLawWoogarooKoalaPopulationConnectivitySnowballExact as Koala

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
  "s3(4) interest affected, s3(6) deemed furnishing by paid post; s5, s11(1)(c),(3)-(5), s13(1),(5), s15(1)-(2), s16 review reasons, applicant-specific furnishing/time, no automatic stay, available discretionary relief. s13 eligibility and notice are distinct from an any-person s135A report request; counsel must check excluded decisions, proper Court route and potential extensions."
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

-- Existing canonical original authorship source. No duplicate source root.
qutLegalAcademicsMarch2026 : Source.AttributedSource
qutLegalAcademicsMarch2026 = Koala.qutCurrentSubmission

qccSpringviewMarch2026 : Source.AttributedSource
qccSpringviewMarch2026 = Koala.qccCurrentSubmission

woogarooCampaignCurrent : Source.AttributedSource
woogarooCampaignCurrent = Source.mkNoDOISource
  "Save Woogaroo Forest campaign"
  "One development approved, another approval looming — take action"
  "Original public campaign advocacy page (undated webpage, accessed October 2026)"
  "October 2026 access, publication date open"
  "https://savewoogarooforest.com.au/action"
  Source.practitionerSource
  "Campaign identifies Stockland/Cherish EPBC 2019/8575 approved and separate Springfield City Group Scenic Precinct EPBC 2020/8651 pending, and invites public funding/contact. Proves claims published by the campaign, not its incorporation/constitution, dated s487 activity series, particular 2019/8575 decision legality, an already filed lawsuit or public funding distribution."
  Source.publicAttribution

nationalEPAEPOOriginal : Source.AttributedSource
nationalEPAEPOOriginal = Source.mkNoDOISource
  "National Environmental Protection Agency"
  "Compliance outcomes: Environment Protection Order under EPBC s474A"
  "Original federal regulator compliance register and actual issued EPO entry"
  "7 October 2026 order; accessed 27 October 2026"
  "https://www.nationalepa.gov.au/epbc/compliance/audit-outcomes"
  Source.governmentSource
  "Section 474A EPO power commenced 24 August 2026; regulator states three threshold beliefs: actual/likely breach, serious damage or imminent risk to the exact protected matter under s474A(2), and necessity. Public register records a real 7 October 2026 EPO concerning Warrengail Pastoral Company / Wombinoo Station. That different-property example proves operation of power, NOT breach at Springfield, approved action 2019/8575, nor EPO for any Woogaroo operator."
  Source.publicAttribution

nationalEPAReportBreachOriginal : Source.AttributedSource
nationalEPAReportBreachOriginal = Source.mkNoDOISource
  "National Environmental Protection Agency"
  "Report a breach of the EPBC Act"
  "Original National EPA regulatory allegation/intake procedure"
  "27 October 2026 access"
  "https://www.nationalepa.gov.au/epbc/compliance/report-a-breach"
  Source.governmentSource
  "The National EPA accepts credible alleged EPBC breaches by web intake (including anonymous), environment.compliance@nationalepa.gov.au and published hotline. It asks for specific locations, maps, time evidence, photos or records; submission does not issue an order, create legal standing, toll court filing periods, or guarantee an investigation or response."
  Source.publicAttribution

nationalEPARulesOriginal : Source.AttributedSource
nationalEPARulesOriginal = Source.mkNoDOISource
  "Minister for the Environment and Water / Commonwealth Federal Register"
  "National Environmental Protection Agency Rules 2026: registrable decisions"
  "Original legislative instrument F2026L01105, registered 21 August"
  "21 August 2026"
  "https://www.legislation.gov.au/F2026L01105/asmade/2026-08-21/text/original/epub/OEBPS/document_1/document_1.html"
  Source.governmentSource
  "Schedule records publication fields for original s474A EPO and s474D variation/revocation. An entry on a register is an identity/status receipt, not proof that other particular premises or actions have been inspected or found to breach EPBC."
  Source.publicAttribution

-- A campaign webpage mixed primary files for distinct controlled actions.
-- The letter's own referral/parcel/date overrides the webpage download label.
scenicGroupDecember2025 : Source.AttributedSource
scenicGroupDecember2025 = Source.mkNoDOISource
  "Save Woogaroo Forest Group Inc.; Keith McCosh, President (printed attribution)"
  "Response on Scenic Precinct, EPBC 2020/8651, Lot 51 SP242316"
  "Original five-page organisation-attributed submission, posted among multi-project campaign submissions"
  "15 December 2025"
  "https://img1.wsimg.com/blobby/go/c204ebbc-02bb-46d9-ad71-ed7d494e752a/downloads/5b140ad8-accf-4ef6-971d-07dc07d315ea/Response%20by%20SWF%20on%20Scenic%208651.pdf?ver=1792152994924"
  Source.communitySource
  "Original PDF pp1 and 5 visually inspected. Names Save Woogaroo Forest Group Inc. and president Keith McCosh IN PRINT (not a visible wet-ink signature), refers ONLY to 2020/8651 Scenic Precinct and 24ha Lot 51. It is evidence of a dated association-authored environmental activity, NOT an ASIC/Queensland incorporation certificate, the association's objects, a second activity, receipt by Department, or the separate Springview 2019/8575 s95B bundle."
  Source.publicAttribution

scenicPossinghamJanuary2025 : Source.AttributedSource
scenicPossinghamJanuary2025 = Source.mkNoDOISource
  "Hugh Possingham"
  "Scenic Precinct EPBC 2020/8651 original ecological submission"
  "Original two-page authored submission; campaign download caption says January 2026"
  "4 January 2025 (date actually printed in original; caption inconsistent)"
  "https://img1.wsimg.com/blobby/go/c204ebbc-02bb-46d9-ad71-ed7d494e752a/downloads/4c22fc2f-3955-4ff9-bdb7-f47767fa6783/Hugh%20Possingham%20submission-Jan%202026.pdf?ver=1792152994924"
  Source.practitionerSource
  "Original PDF p1 visually checked: address to Springfield City Group and subject EPBC 2020/8651, 24.2ha Lot 51. Printed 4 Jan 2025 within s487 15 Oct 2024–2026 window, but actual signature/dispatch/date must be corroborated if disputed. NOT direct objection submitted under EPBC 2019/8575."
  Source.publicAttribution

scenicZdenekDecember2025 : Source.AttributedSource
scenicZdenekDecember2025 = Source.mkNoDOISource
  "Christina N. Zdenek"
  "Scenic Precinct EPBC 2020/8651 original ecological submission"
  "Original four-page authored submission; campaign download caption says January 2026"
  "14 December 2025 (date actually printed in original)"
  "https://img1.wsimg.com/blobby/go/c204ebbc-02bb-46d9-ad71-ed7d494e752a/downloads/321ec662-92cb-49d8-8588-8b237e8fc4f3/Dr%20Christina%20Zdenek%20submission-Jan%202026.pdf?ver=1792152994924"
  Source.practitionerSource
  "Original PDF p1 visually checked: exact EPBC 2020/8651, Lots 51 and 50, NOT 2019/8575. The printed 14 Dec 2025 is prior environmental advocacy and a research witness locator, NOT proof it was received, a group activity, or same-parcel impact."
  Source.publicAttribution

swfgAustralianBusinessRegister : Source.AttributedSource
swfgAustralianBusinessRegister = Source.mkNoDOISource
  "Australian Business Register / Australian Taxation Office"
  "ABN 86 248 330 120 — Save Woogaroo Forest Group Inc"
  "Original Commonwealth ABN Lookup, details last updated 21 Nov 2024"
  "17 November 2024 (ABN active-from date, NOT legal commencement certificate)"
  "https://abr.business.gov.au/ABN/View?id=86248330120"
  Source.governmentSource
  "ABR authoritative entry reports exact entity name, active ABN from 17 Nov 2024, Other Incorporated Entity, main QLD 4300, no DGR. It is a positive identity/form lead, NOT an incorporated-associations register extract, its governing objects at 15 Oct 2026, authority to sue, or proof of all EPBC s487 conditions."
  Source.publicAttribution

senateWoogarooPetition2025 : Source.AttributedSource
senateWoogarooPetition2025 = Source.mkNoDOISource
  "Parliament of Australia — Australian Senate"
  "Senate Daily Summary 25–26 March 2025: petitioning document about koalas of Woogaroo Forest"
  "Official Senate chamber daily summary"
  "26 March 2025"
  "https://www.aph.gov.au/Parliamentary_Business/Chamber_documents/Senate_chamber_documents/sds/Archive/2025/Senate_Daily_Summary_-_25_to_26_March_2025"
  Source.governmentSource
  "Senator Waters tabled a petitioning document relating to koalas of Woogaroo Forest. Parliamentary event and date identified. The original summary does NOT identify SWFG as the organiser or author, give signature total, certify its objects, identify a litigant, or prove s95B receipt for 2019/8575."
  Source.publicAttribution

ipswichJuly2025CampaignCoverage : Source.AttributedSource
ipswichJuly2025CampaignCoverage = Source.mkNoDOISource
  "Rowan Anderson / Local Ipswich News"
  "International conservation group visits to support green corridor"
  "Original contemporaneous local reporting naming Save Woogaroo Forest Group Inc."
  "17 July 2025"
  "https://localipswichnews.com.au/news/woogaroo-forest-campaign/"
  Source.newsSource
  "Dated report documents campaign activity and a group spokesperson, and describes expert site visits. This is secondary corroboration distinct from the original December 2025 SWFG submission, NOT the original association constitution or primary scientific measurements. Check underlying campaign records if relied upon for s487 activity-series proof."
  Source.publicAttribution

------------------------------------------------------------------------
-- Original documentary retrieval + actual Federal Court standing PLEADINGS.
-- Court-filed Form 66 originals show legal arguments raised by applicants;
-- they are NOT a court holding, successful stay or same-project evidence.
------------------------------------------------------------------------

qldOFTAssociationFileAcquisition : Source.AttributedSource
qldOFTAssociationFileAcquisition = Source.mkNoDOISource
  "Queensland Office of Fair Trading"
  "Request information about an incorporated association"
  "Original Queensland register and lodged-document access instructions"
  "28 October 2026 access"
  "https://www.qld.gov.au/community/fair-trading/associations-charities-and-not-for-profits/incorporated-associations/request-information-about-an-incorporated-association"
  Source.governmentSource
  "OFT supplies association extract (name, address, committee history and lodged-document list), certified incorporation certificate, registered rules, amendments, annual returns and committee changes for a fee. Original guidance states an ordinary ~10 working day retrieval. SWFG 15 Oct 2026 governing objects and members cannot be reconstructed from an ABN, future amendments or presumed model rules."
  Source.publicAttribution

qldOFTCurrentRules : Source.AttributedSource
qldOFTCurrentRules = Source.mkNoDOISource
  "Queensland Office of Fair Trading"
  "Rules for associations — governing objects and historical approval"
  "Original Queensland association rules guidance"
  "28 October 2026 access"
  "https://www.qld.gov.au/community/fair-trading/associations-charities-and-not-for-profits/incorporated-associations/running-an-incorporated-association/rules-for-associations"
  Source.governmentSource
  "OFT: associations must lodge rules; both model and own rules must state objects; own rules amendments require approval by OFT and take effect when approved. Demand applicable ORIGINAL approved rules/version on 15 October 2026, not online model text. A future replacement is not automatically retrospective."
  Source.publicAttribution

qldOFT2026Fees : Source.AttributedSource
qldOFT2026Fees = Source.mkNoDOISource
  "Queensland Office of Fair Trading"
  "Fair trading fees — 2026 incorporated-association document access"
  "Original QLD price list updated 1 July 2026"
  "1 July 2026"
  "https://www.qld.gov.au/community/fair-trading/associations-charities-and-not-for-profits/fair-trading-fees"
  Source.governmentSource
  "Public 2026 prices: AUD 9 association/charity file retrieval, AUD 4.20 per photocopied page, AUD 28.85 certified incorporation certificate. These are acquisition fees, NOT development infrastructure charges, public assistance or litigation costs."
  Source.publicAttribution

federalCourtFriendsRockArt2026Form66 : Source.AttributedSource
federalCourtFriendsRockArt2026Form66 = Source.mkNoDOISource
  "Friends of Australian Rock Art Inc (applicant); Federal Court of Australia (filed record)"
  "VID1357/2025 — amended Form 66, filed 13 March 2026"
  "Original Court-hosted, filed and amended originating application, not judgment"
  "13 March 2026"
  "https://www.fedcourt.gov.au/__data/assets/pdf_file/0004/596038/2026-03-13_Originating-Application-for-Judicial-Review-Form-66-Rule-31.011_E5530476_v1.pdf"
  Source.governmentSource
  "Federal Court original PDF page 3 (zero-index 2) visually inspected: applicant PLEADS s487(3) Australian incorporation, environmental activities in two years before its September 2025 NWS decision, and environmental objects in rules at decision date, in ADJR s5 and Judiciary Act s39B proceeding. This is applicant allegation and permissible procedural template, NOT decided standing, law on Woogaroo, a precedent ratio, or an injunction."
  Source.publicAttribution

federalCourtACF2026Form66 : Source.AttributedSource
federalCourtACF2026Form66 = Source.mkNoDOISource
  "Australian Conservation Foundation Inc (applicant); Federal Court of Australia (filed record)"
  "VID1356/2025 — amended Form 66 dated 26 February 2026"
  "Original Court-hosted originating application, not judicial reasons"
  "26 February–2 March 2026 (lodged/accepted)"
  "https://www.fedcourt.gov.au/__data/assets/pdf_file/0009/596025/2026-02-27_Originating-Application-for-Judicial-Review-Form-66-Rule-31.011_E5471674_v1.pdf"
  Source.governmentSource
  "Original Court PDF page 3 (zero-index 2) visually checked. ACF pleads ACT incorporation, 2-year series with public submissions, letters and an expert report, and constitution's environmental objects to assert s487(3) standing in a separate North West Shelf case. A pleading is a claim by a party; NOT a judicial determination, evidence SWFG did those same activities, or precedent deciding how many activities satisfy s487."
  Source.publicAttribution

springfieldFeb2026CommentInvitation : Source.AttributedSource
springfieldFeb2026CommentInvitation = Source.mkNoDOISource
  "Cherish Enterprises Pty Ltd / Saunders Havill (proponent notice)"
  "Original s95A(3) invitation for EPBC 2019/8575 public comment"
  "Original one-page project invitation via Commonwealth EPBC public portal"
  "13 February–12 March 2026"
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/4f8edc14-9ffb-ee11-9f89-00224892a860/2ab10dab-d681-4911-b881-cc99413f07b6?file=2019-8575-Draft-PD.pdf"
  Source.practitionerSource
  "Original PDF page 1 visually checked: s95A(3) invites comments on EPBC 2019/8575 13 February–12 March 2026; submissions directed to epbc@springfieldresidential.com or 9 Thompson Street Bowen Hills. Portal file is a ONE-PAGE INVITATION, NOT actual full Draft PD, received proponent inbox, 1,786 individual comments, final s95B response or Secretary s95C recommendation. Request original server/post logs and transmitted copies, not an assumed Minister direct-email receipt."
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
  nationalEPASection474AComplianceOrder : ProtectionRoute
  nationalEPAReportBreachIntake : ProtectionRoute

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

qutLetterEvidenceLead : LitigationGate
qutLetterEvidenceLead = litigation-gate adjrSection5Review qutLegalAcademicsMarch2026
  caseSpecificProofOpen
  "Three specifically named QUT legal academics signed a 12 March 2026 objection about EPBC 2019/8575; dated original environmental advocacy expression and specific ecology assertions."
  "Obtain any relevant authors' own further 2024-2026 environmental activities and consent to potential witness role; locate original sending/receipt/transmission before alleging Minister considered or omitted the letter."
  false refl

campaignActivityLead : LitigationGate
campaignActivityLead = litigation-gate adjrSection5Review woogarooCampaignCurrent
  caseSpecificProofOpen
  "Save Woogaroo Forest first-party webpage states live advocacy and a funding appeal relating to two DISTINCT EPBC actions 2019/8575 and 2020/8651."
  "Original dated two-year campaign organisational activity, 15 Oct constitution/purposes, actual committee resolution and applicant representation; a website heading does not prove s487 standing or that a Federal Court case was commenced."
  false refl

-- Administrative/CEO enforcement is NOT a litigant-initiated injunction.
-- Reuse the generic evidence gate as a route inventory; the applicant/decision
-- maker distinction is encoded in the route and its missing-proof field.
nationalEPA474AEnforcement : LitigationGate
nationalEPA474AEnforcement = litigation-gate nationalEPASection474AComplianceOrder nationalEPAEPOOriginal
  caseSpecificProofOpen
  "National EPA CEO (not a conservation group or Federal Court) may issue EPBC s474A Environment Protection Order when all statutory beliefs concern actual/likely breach, serious damage or imminent risk to a protected matter under s474A(2), and necessity. 14-day short term; possible one extension. Existing 7 Oct Warrengail order is a separate-property example."
  "Original 15 Oct 2026 approval conditions for referral 2019/8575; same-area works, identified conduct/date, specific probable approval-condition/Act contravention, serious damage or imminent risk to a protected matter under s474A(2), CEO necessity and person lawfully subject to EPO. Original C70 Volume 3 s474A pages 107-108 and s474D page 111 visually checked."
  false refl

nationalEPAComplianceReport : LitigationGate
nationalEPAComplianceReport = litigation-gate nationalEPAReportBreachIntake nationalEPAReportBreachOriginal
  caseSpecificProofOpen
  "An informant can submit a genuine suspected-breach report to the National EPA, including with documentary proof and optionally anonymously. Regulator independently evaluates any order/audit/investigation."
  "Dated conduct with precise site and its credible statutory breach nexus, safe collection of original photos/videos/maps, and delivery acknowledgment if actually submitted; no allegation of a 2019/8575 EPO unless register pays it."
  false refl

ePoPublicationRequirement : Source.AttributedSource
ePoPublicationRequirement = nationalEPARulesOriginal

-- Same-action ecology is reused from an existing source owner; a letter
-- signed and publicly posted is not yet a s95B transmission receipt.
qccSameCaseSubmissionLead : LitigationGate
qccSameCaseSubmissionLead = litigation-gate adjrSection5Review qccSpringviewMarch2026
  caseSpecificProofOpen
  "12 March 2026 QCC original signed submission, Anthony Gough acting director, names EPBC 2019/8575 and Woogaroo Creek–Opossum Creek connectivity. This source is already owned by the KoalaPopulationConnectivity module."
  "Confirm actual s95B public-comment delivery to Minister, full QCC activity/objects and correct applicant identity. QCC as a separate legal person does not pay SWFG standing or plaintiff status."
  false refl

swfgScenicStandingActivityLead : LitigationGate
swfgScenicStandingActivityLead = litigation-gate adjrSection5Review scenicGroupDecember2025
  caseSpecificProofOpen
  "A 15 Dec 2025 dated response expressly names Save Woogaroo Forest Group Inc. and president Keith McCosh for separate EPBC 2020/8651, providing one original organisational environmental activity in the pre-15 Oct 2026 two-year window."
  "Association incorporation certificate and constitution/objects as at 15 Oct, dated series of environmental activities rather than a single letter, actual signatory's authority, submission dispatch/receipt and board litigation authorisation."
  false refl

possinghamScenicActivityLead : LitigationGate
possinghamScenicActivityLead = litigation-gate adjrSection5Review scenicPossinghamJanuary2025
  caseSpecificProofOpen
  "The original Hugh Possingham submission is labelled EPBC 2020/8651 and printed 4 Jan 2025 despite website link title Jan 2026; distinct scientific author/environment activity witness lead."
  "Verify original dispatch/author confirmation before relying on date; separate proof of any candidate individual's citizenship/residency and two-year series; neither this letter nor its science proves 2019/8575 legal invalidity."
  false refl

zdenekScenicActivityLead : LitigationGate
zdenekScenicActivityLead = litigation-gate adjrSection5Review scenicZdenekDecember2025
  caseSpecificProofOpen
  "Christina Zdenek's original submission is internally dated 14 Dec 2025, names 2020/8651 and 24.2ha, even though the campaign labels its download Jan 2026."
  "Obtain provenance, recipient delivery and individual's own complete statutory standing evidence; keep 2020/8651 science and location separate from 2019/8575."
  false refl

swfgABNOrganisationIdentityLead : LitigationGate
swfgABNOrganisationIdentityLead = litigation-gate adjrSection5Review swfgAustralianBusinessRegister
  caseSpecificProofOpen
  "ABR identifies Save Woogaroo Forest Group Inc, ABN 86 248 330 120, as an Other Incorporated Entity and active since 17 November 2024 in QLD; materially stronger entity identity than website alone."
  "Acquire actual Queensland incorporated-association registration/historical rules and objects as on decision date 15 Oct 2026, capacity and authorised court applicant; ABN record is not a certificate of objects."
  false refl

swfgMarch2025PublicPetitionLead : LitigationGate
swfgMarch2025PublicPetitionLead = litigation-gate adjrSection5Review senateWoogarooPetition2025
  caseSpecificProofOpen
  "Official Senate daily summary says Senator Waters tabled a petition concerning Woogaroo koalas in March 2025, within the two-year s487 environmental-activity period."
  "Actual petition original and sponsor/organiser records naming the group; do NOT assign Senate event to SWFG organisational acts from geographic theme or 15,000 reported signatures alone."
  false refl

swfgJuly2025CampaignSeriesLead : LitigationGate
swfgJuly2025CampaignSeriesLead = litigation-gate adjrSection5Review ipswichJuly2025CampaignCoverage
  caseSpecificProofOpen
  "17 July 2025 contemporaneous report identifies SWFG Inc conservation campaign, spokesperson and group-linked expert visit; distinct date/medium from its authored 15 Dec 2025 Scenic submission."
  "Original SWFG event announcement, organiser records and legally admissible witnesses; find full activity chronology and objects rather than claim standing final."
  false refl

qldOFTRulesDecisionDateCut : LitigationGate
qldOFTRulesDecisionDateCut = litigation-gate adjrSection5Review qldOFTAssociationFileAcquisition
  caseSpecificProofOpen
  "Queensland OFT original has a paid extracts/file/certificate process identifying actual objects and committee history. It generally reports a 10-working-day retrieval; parallel urgent counsel required."
  "SWFG registration number/extract, certified incorporation and historic approved rules in force at 15 Oct 2026, any amendments with approval-effective dates, committee and valid proceedings authorisation."
  false refl

qldOFTVersionAndFeeCut : LitigationGate
qldOFTVersionAndFeeCut = litigation-gate adjrSection5Review qldOFTCurrentRules
  caseSpecificProofOpen
  "QLD original requires environmental objects in actual approved association rules and states rule amendments take effect on approval. Published 2026 rates from a distinct OFT original are AUD 9 file, AUD 4.20 per page, AUD 28.85 certified incorporation."
  "Request/receipt and applicable 15 Oct 2026 adopted version, not a downloaded model-rule default; collect original amendment dates and payment receipt only if actually made."
  false refl

filedStandingComparatorCut : LitigationGate
filedStandingComparatorCut = litigation-gate adjrSection5Review federalCourtFriendsRockArt2026Form66
  caseSpecificProofOpen
  "Court-filed 13 Mar 2026 original amended Form 66 in VID1357/2025 pleads association s487(3) three limbs, ADJR s5 and possible s39B against a wholly DIFFERENT NWS action."
  "Actual SWFG objects, series and form of standing evidence; counsel must verify right grounds/proceeding parties and current applicable court rules. No judgment in this downloaded source."
  false refl

acfConstitutionActivitiesComparatorCut : LitigationGate
acfConstitutionActivitiesComparatorCut = litigation-gate adjrSection5Review federalCourtACF2026Form66
  caseSpecificProofOpen
  "ACF's separate amended NWS Form 66 in VID1356/2025 pleads dated ministerial letters/submissions/expert report and constitutional purposes as its s487(3) case."
  "Actual SWFG activity exhibits with original authors, at-decision constitution and legitimate plaintiff authority; ACF's assertions cannot substitute for evidence or outcome."
  false refl

proponentInboxMarch2026Cut : LitigationGate
proponentInboxMarch2026Cut = litigation-gate adjrSection5Review springfieldFeb2026CommentInvitation
  caseSpecificProofOpen
  "Original 2019/8575 s95A invitation directs comments to epbc@springfieldresidential.com or 9 Thompson Street by 12 March 2026, not to an automatic Minister public-email channel."
  "QUT/QCC sender dispatch, project inbox/mail delivery and logs, full individual comment inventory, s95B(1)(b)(ii) proponent-to-Minister package and final response, plus signed decision file."
  false refl

triageGates : List LitigationGate
triageGates =
  individualStanding ∷ organisationStanding ∷ independentAffectedInterest ∷
  section39BAlternative ∷ furnishingClock ∷ stayAfterFiling ∷
  epbcContravention ∷ beforeOriginating ∷ undertakingRisk ∷
  qutLetterEvidenceLead ∷ campaignActivityLead ∷
  nationalEPA474AEnforcement ∷ nationalEPAComplianceReport ∷
  qccSameCaseSubmissionLead ∷ swfgScenicStandingActivityLead ∷
  possinghamScenicActivityLead ∷ zdenekScenicActivityLead ∷
  swfgABNOrganisationIdentityLead ∷ swfgMarch2025PublicPetitionLead ∷
  swfgJuly2025CampaignSeriesLead ∷
  qldOFTRulesDecisionDateCut ∷ qldOFTVersionAndFeeCut ∷
  filedStandingComparatorCut ∷ acfConstitutionActivitiesComparatorCut ∷
  proponentInboxMarch2026Cut ∷ []

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
data OriginalSubmissionAddressedToMinisterProvesSection95BReceipt : Set where
data CampaignFundingAppealEqualsFiledCourtProceeding : Set where
data August2026EPOPowerMeansAutomaticWoogarooProtection : Set where
data OtherPropertyOctoberEPOProvesThisCaseBreach : Set where
data RegulatorIntakeEqualsCourtStayOrReportDelivery : Set where
data EPOCanIssueForLawfulApprovedClearingWithoutBreach : Set where
data Scenic20208651SubmissionsAreSpringview20198575Comments : Set where
data DatedOneAssociationLetterProvesFullSection487Standing : Set where
data CampaignDownloadCaptionOverridesOriginalPrintedDate : Set where
data QCCSubmissionProvesSWFGGroupStanding : Set where
data ABNEntryProvesSection487ObjectsAtDecision : Set where
data SenatePetitionAboutWoogarooProvesSWFGOrganisedIt : Set where
data OFTModelRulesAreSWFGObjectsAtDecision : Set where
data ABNAndLaterRulesProveHistoricAssociationObjects : Set where
data OtherAssociationFiledForm66IsCourtHoldingForSWFG : Set where
data PublicCourtPleadingEqualsJudiciallySuccessfulOutcome : Set where
data ProponentInvitationMeansQUTAndQCCCommentsDelivered : Set where
data DocumentRetrievalRequestStopsFederalCourtTime : Set where

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

addressedLetterNotProvenReceipt :
  OriginalSubmissionAddressedToMinisterProvesSection95BReceipt → ⊥
addressedLetterNotProvenReceipt ()

campaignAppealNotLitigation :
  CampaignFundingAppealEqualsFiledCourtProceeding → ⊥
campaignAppealNotLitigation ()

epoPowerNotAutomaticallySiteProtection :
  August2026EPOPowerMeansAutomaticWoogarooProtection → ⊥
epoPowerNotAutomaticallySiteProtection ()

warrengailDifferentFromWoogaroo :
  OtherPropertyOctoberEPOProvesThisCaseBreach → ⊥
warrengailDifferentFromWoogaroo ()

complaintNotCourtOrOrder :
  RegulatorIntakeEqualsCourtStayOrReportDelivery → ⊥
complaintNotCourtOrOrder ()

lawfulClearingNotAutomaticallyEPOCase :
  EPOCanIssueForLawfulApprovedClearingWithoutBreach → ⊥
lawfulClearingNotAutomaticallyEPOCase ()

scenicNotSpringviewComment :
  Scenic20208651SubmissionsAreSpringview20198575Comments → ⊥
scenicNotSpringviewComment ()

oneLetterNotSection487Series :
  DatedOneAssociationLetterProvesFullSection487Standing → ⊥
oneLetterNotSection487Series ()

originalDateBeatsCaption :
  CampaignDownloadCaptionOverridesOriginalPrintedDate → ⊥
originalDateBeatsCaption ()

qccNotSwfgStanding :
  QCCSubmissionProvesSWFGGroupStanding → ⊥
qccNotSwfgStanding ()

abnNoObjectsCertification : ABNEntryProvesSection487ObjectsAtDecision → ⊥
abnNoObjectsCertification ()

senateThemeNotGroupOrganiser :
  SenatePetitionAboutWoogarooProvesSWFGOrganisedIt → ⊥
senateThemeNotGroupOrganiser ()

noDefaultSWFGRules : OFTModelRulesAreSWFGObjectsAtDecision → ⊥
noDefaultSWFGRules ()

notRetrospectiveAssociationObjects :
  ABNAndLaterRulesProveHistoricAssociationObjects → ⊥
notRetrospectiveAssociationObjects ()

otherCaseFormNotSWFGStanding :
  OtherAssociationFiledForm66IsCourtHoldingForSWFG → ⊥
otherCaseFormNotSWFGStanding ()

pleadingNotJudgment :
  PublicCourtPleadingEqualsJudiciallySuccessfulOutcome → ⊥
pleadingNotJudgment ()

invitationNotDeliveredComments :
  ProponentInvitationMeansQUTAndQCCCommentsDelivered → ⊥
invitationNotDeliveredComments ()

paidFileRequestNotTimeStop :
  DocumentRetrievalRequestStopsFederalCourtTime → ⊥
paidFileRequestNotTimeStop ()
