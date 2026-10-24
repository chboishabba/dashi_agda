module DASHI.Cognition.EpsteinBlackApolloSameObjectReceiptRound20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBankingInfrastructureAcquisitionExact as Banking
import DASHI.Cognition.EpsteinFinanceTechParetoRoundExact as Finance

------------------------------------------------------------------------
-- EPSTEIN / LEON BLACK / APOLLO SAME-OBJECT RECEIPT ROUND — 2026-10-14
--
-- The central correction is that "Apollo never retained Epstein" and
-- "Epstein had no Apollo-related financial edge" are not equivalent claims.
-- The public record supports several narrow Apollo-related coordinates while
-- still supporting the absence of an Epstein investment in Apollo-managed
-- funds and the absence of an Apollo corporate retainer for Epstein.
------------------------------------------------------------------------

data BlackApolloSurface : Set where
  personalAdvisory : BlackApolloSurface
  blackFamilyOffice : BlackApolloSurface
  apolloOwnershipInterestTaxPlanning : BlackApolloSurface
  apolloPublicEquity : BlackApolloSurface
  apolloExecutiveSideVehicle : BlackApolloSurface
  coInvestmentWithBlackFamily : BlackApolloSurface
  professionalServicePayment : BlackApolloSurface
  loan : BlackApolloSurface
  philanthropy : BlackApolloSurface
  bankProcessing : BlackApolloSurface
  congressionalFinding : BlackApolloSurface

record SameObjectReceipt : Set where
  constructor same-object-receipt
  field
    label : String
    surface : BlackApolloSurface
    source : String
    boundedFinding : String
    primaryOrOfficial : Bool
    relationPaid : Bool
    apolloCorporateRetainerPaid : Bool
    apolloManagedFundInvestmentPaid : Bool
    wrongdoingPaidByThisReceipt : Bool
open SameObjectReceipt public

blackEpsteinAdvisory158m : SameObjectReceipt
blackEpsteinAdvisory158m = same-object-receipt
  "Dechert Black-Epstein advisory total"
  professionalServicePayment
  "SEC-filed Dechert report, 2021-01-22"
  "The Apollo Conflicts Committee review found Black paid Epstein USD 158 million from 2013 through 2017 for tax, estate-planning and related Family Office advice. The report attributes USD 50m to 2013, USD 70m to 2014, USD 30m to 2015, no payment in 2016 and USD 8m in April 2017."
  true true false false false

senateBlackEpstein170m : SameObjectReceipt
senateBlackEpstein170m = same-object-receipt
  "Senate/Treasury Black-Epstein payment total"
  congressionalFinding
  "Senate Finance letter to DOJ/Treasury/FBI, 2025-03-11; 2026 follow-up"
  "Senate Finance states federal records identified additional wire transfers omitted from the Dechert total and place Black-controlled-account payments to Epstein entities at more than USD 170 million. This is an attributed congressional finding based on Treasury records and does not silently rewrite the narrower Dechert service-fee ledger."
  true true false false false

blackAccountsToEpsteinEntities : SameObjectReceipt
blackAccountsToEpsteinEntities = same-object-receipt
  "Black-controlled accounts to Southern/Financial Trust"
  bankProcessing
  "Senate Finance Treasury-record review, 2025-03-11"
  "Senate Finance states Black-controlled accounts including Leon Black, Debra Black, Black Family Partners LP, Narrows Holdings LLC, Elysium Management LLC and Melanie Spinella sent roughly USD 170m to Epstein-controlled Southern Trust Company and Financial Trust Company; about USD 140m was transferred to Southern Trust accounts at Deutsche Bank during 2013-2015."
  true true false false false

blackSouthernTrust2013Contract : SameObjectReceipt
blackSouthernTrust2013Contract = same-object-receipt
  "Black-Southern Trust written services agreement"
  personalAdvisory
  "SEC-filed Dechert report, 2021-01-22"
  "A February 2013 agreement between Black and Epstein affiliate Southern Trust Company covered estate-planning services; Dechert records USD 15m and USD 8.5m installment payments in 2013."
  true true false false false

blackEpsteinLoans2017 : SameObjectReceipt
blackEpsteinLoans2017 = same-object-receipt
  "BV70-to-Plan D loans"
  loan
  "SEC-filed Dechert report, 2021-01-22"
  "Black-owned BV70 LLC made two documented early-2017 loans of USD 22.5m and USD 8m to Epstein-owned Plan D LLC in connection with an art transaction; Epstein repaid USD 10m and the remainder was unpaid at his death according to Dechert. These loans are separate from service fees."
  true true false false false

blackGratitudeAmericaDonation : SameObjectReceipt
blackGratitudeAmericaDonation = same-object-receipt
  "Black donation to Epstein-affiliated Gratitude America"
  philanthropy
  "SEC-filed Dechert report, 2021-01-22"
  "Dechert found Black made a USD 10m donation to Epstein-affiliated Gratitude America in October 2015 and records additional philanthropy at Epstein's request; a separate alleged USD 5m Gratitude America donation had a thank-you letter/email but no Black-side bank record located by Dechert."
  true true false false false

epsteinApolloIPOStock : SameObjectReceipt
epsteinApolloIPOStock = same-object-receipt
  "Epstein entity Apollo IPO stock purchase"
  apolloPublicEquity
  "SEC-filed Dechert report, 2021-01-22"
  "Dechert found Epstein-owned Financial Trust Company purchased 263,257 Apollo shares in Apollo's 2011 IPO through the directed-share program; the shares appear to have transferred in 2013 to Epstein-affiliated Southern Financial LLC and remained there through at least September 2019. This is Apollo public-equity exposure, not an Apollo-managed-fund investment or corporate retainer."
  true true false false false

epsteinApolloExecutiveSideVehicles : SameObjectReceipt
epsteinApolloExecutiveSideVehicles = same-object-receipt
  "Epstein passive investment alongside Apollo executives"
  apolloExecutiveSideVehicle
  "SEC-filed Dechert report, 2021-01-22"
  "Dechert found Financial Trust Company invested in AP SHL Investors LLC and AP Technology Partners LLC, vehicles formed by certain Apollo executives to explore opportunities Apollo chose not to pursue. The report says these were not Apollo entities and found Epstein to be a passive investor."
  true true false false false

epsteinESWWCoInvestment : SameObjectReceipt
epsteinESWWCoInvestment = same-object-receipt
  "Epstein/Black-family ESWW co-investment"
  coInvestmentWithBlackFamily
  "SEC-filed Dechert report, 2021-01-22"
  "Dechert found Financial Trust Company appears to have invested in Environmental Solutions World Wide in 2011 alongside Black and certain Black family members. This pays a co-investment edge and nothing more."
  true true false false false

epsteinApolloOwnershipTaxAdvice : SameObjectReceipt
epsteinApolloOwnershipTaxAdvice = same-object-receipt
  "Epstein advice on Black Apollo ownership-interest tax filings"
  apolloOwnershipInterestTaxPlanning
  "SEC-filed Dechert report; Senate Finance 2023 trust inquiry"
  "Dechert states Epstein helped manage tax-compliance issues relating to BRH Holdings LP, the partnership through which Black and other Apollo co-founders held Apollo ownership interests. Senate Finance separately states Black's 2006 GRATs were funded by large percentage interests in multiple Apollo management/advisory partnerships. This pays an Apollo-ownership-interest tax-planning coordinate through Black's personal/family structures, not an Apollo corporate retainer."
  true true false false false

apolloNoCorporateRetainer : SameObjectReceipt
apolloNoCorporateRetainer = same-object-receipt
  "No Apollo corporate retainer identified"
  personalAdvisory
  "SEC-filed Dechert report; Apollo 2026 client letter"
  "Dechert reported no indication Apollo ever retained Epstein and no Epstein investment in Apollo-managed funds; Apollo repeated in 2026 that Black was the only Apollo principal with the paid personal advisory relationship, while noting that select Apollo employees supplied information connected to Black's tax work. This bounded negative does not erase the IPO-stock, side-vehicle, ownership-interest-tax or introduction edges."
  true true false false false

record ApolloNuanceBoundary : Set where
  constructor apollo-nuance-boundary
  field
    epsteinHeldApolloPublicEquity : Bool
    epsteinInvestedInApolloManagedFund : Bool
    apolloCorporationRetainedEpstein : Bool
    epsteinAdvisedOnBlackApolloOwnershipInterests : Bool
    epsteinInvestedAlongsideSomeApolloExecutives : Bool
    blackTriedToIntroduceEpsteinToCoFounders : Bool
    theseEdgesEqualApolloCorporateEngagement : Bool
    apolloNegativeStatementErasesNarrowEdges : Bool
open ApolloNuanceBoundary public

canonicalApolloNuanceBoundary : ApolloNuanceBoundary
canonicalApolloNuanceBoundary = apollo-nuance-boundary
  true false false true true true false false

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data PublicEquityImpliesCorporateRetainer : Set where
data SideVehicleImpliesApolloFund : Set where
data OwnershipTaxAdviceImpliesApolloClient : Set where
data IntroductionAttemptImpliesRetention : Set where
data CongressionalWireFindingImpliesCriminalConviction : Set where
data LargePaymentImpliesIllicitPurpose : Set where
data USVISettlementImpliesAdmissionOfAllAllegations : Set where

publicEquityDoesNotCreateRetainer : PublicEquityImpliesCorporateRetainer → ⊥
publicEquityDoesNotCreateRetainer ()

sideVehicleDoesNotCreateApolloFund : SideVehicleImpliesApolloFund → ⊥
sideVehicleDoesNotCreateApolloFund ()

ownershipTaxAdviceDoesNotCreateApolloClient : OwnershipTaxAdviceImpliesApolloClient → ⊥
ownershipTaxAdviceDoesNotCreateApolloClient ()

introductionAttemptDoesNotCreateRetention : IntroductionAttemptImpliesRetention → ⊥
introductionAttemptDoesNotCreateRetention ()

congressionalWireFindingDoesNotCreateConviction : CongressionalWireFindingImpliesCriminalConviction → ⊥
congressionalWireFindingDoesNotCreateConviction ()

largePaymentDoesNotCreateIllicitPurpose : LargePaymentImpliesIllicitPurpose → ⊥
largePaymentDoesNotCreateIllicitPurpose ()

usviSettlementDoesNotCreateUniversalAdmission : USVISettlementImpliesAdmissionOfAllAllegations → ⊥
usviSettlementDoesNotCreateUniversalAdmission ()

------------------------------------------------------------------------
-- Remaining acquisition is now transaction-object specific.
------------------------------------------------------------------------

data BlackApolloDebt : Set where
  exact170mWireLedger : BlackApolloDebt
  additional12mWirePurpose : BlackApolloDebt
  apolloIPOShareDispositionAfter2019 : BlackApolloDebt
  apSHLAndAPTechnologyUnderlyingDeals : BlackApolloDebt
  eswwPositionAndExit : BlackApolloDebt
  gratApolloInterestCurrentDisposition : BlackApolloDebt
  blackFamilyOfficeAdvisorCounterpartyGraph : BlackApolloDebt
  bankEmployeeDecisionChainForBlackWires : BlackApolloDebt
  black2026TranscriptReconciliation : BlackApolloDebt

record BlackApolloAcquisition : Set where
  constructor black-apollo-acquisition
  field
    debt : BlackApolloDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open BlackApolloAcquisition public

canonicalBlackApolloAcquisition : List BlackApolloAcquisition
canonicalBlackApolloAcquisition =
  black-apollo-acquisition exact170mWireLedger 100 true
    "Recover the Treasury/SAR-level Black->Epstein wire ledger with date, payer account/entity, sending bank, recipient entity/bank, amount and stated/purported purpose; reconcile the Dechert USD 158m service ledger with Senate Finance's >USD 170m transaction total."
  ∷ black-apollo-acquisition additional12mWirePurpose 100 true
    "Resolve the additional wires totaling about USD 12m that Senate Finance says were absent from the Apollo/Dechert review, including purpose and whether they were fees, gifts, loans, reimbursements or another class."
  ∷ black-apollo-acquisition bankEmployeeDecisionChainForBlackWires 99 true
    "Identify the specific bank compliance/relationship-management chain that cleared, reviewed or delayed reporting Black-account wires to Epstein entities and distinguish institutional findings from individual knowledge."
  ∷ black-apollo-acquisition gratApolloInterestCurrentDisposition 99 true
    "Trace the Apollo management/advisory interests placed in Black's 2006 GRATs through valuations, distributions, retained voting/control rights and later disposition."
  ∷ black-apollo-acquisition blackFamilyOfficeAdvisorCounterpartyGraph 98 true
    "Map Paul Weiss, accounting/tax advisers, Elysium/Family Office personnel and other counterparties who originated, vetted, implemented or rejected each Epstein-proposed structure."
  ∷ black-apollo-acquisition apSHLAndAPTechnologyUnderlyingDeals 98 true
    "Resolve capitalization, managers, co-investors, investments and exits for AP SHL Investors and AP Technology Partners; keep them explicitly non-Apollo unless a formal Apollo relationship is independently paid."
  ∷ black-apollo-acquisition apolloIPOShareDispositionAfter2019 97 true
    "Trace the 263,257 Apollo IPO shares from Financial Trust Company to Southern Financial LLC and determine disposition/value after September 2019, including estate treatment."
  ∷ black-apollo-acquisition eswwPositionAndExit 96 true
    "Resolve Epstein's ESWW investment amount, Black/family co-investment structure, board/governance rights if any and exit chronology."
  ∷ black-apollo-acquisition black2026TranscriptReconciliation 95 true
    "Reconcile Black's June 2026 House Oversight testimony against Dechert, Senate Finance/Treasury and USVI settlement records claim by claim."
  ∷ []

------------------------------------------------------------------------
-- 2026 WYDEN FOLLOW-UP: ATTRIBUTED CONGRESSIONAL INVESTIGATIVE QUESTIONS,
-- NOT ADJUDICATED CRIMINAL OR TAX LIABILITY.
-- This supplements (does not replace) the original Dechert, Senate/Treasury
-- and DOJ-EFTA payment/work-product owners already in the Black atlas.
------------------------------------------------------------------------

data Wyden2026Question : Set where
  comparativeProfessionalCompensation : Wyden2026Question
  allegedIntermediatedPaymentsToWomen : Wyden2026Question
  allegedSurveillanceOfWomen : Wyden2026Question
  giftTaxAndCharityQuestions : Wyden2026Question

record Wyden2026ClaimReceipt : Set where
  constructor wyden-2026-claim-receipt
  field
    questionedIssue : Wyden2026Question
    originalCongressionalLocator : String
    documentaryReference : String
    narrowAttribution : String
    congressionalQuestionLocated : Bool
    sourceUnderlyingItemInspectedForThisClaim : Bool
    independentLiabilityOrCriminalVerdictPaid : Bool
    linksToBannonFilmProgrammePaid : Bool
open Wyden2026ClaimReceipt public

wydenWomenPaymentsQuestion : Wyden2026ClaimReceipt
wydenWomenPaymentsQuestion = wyden-2026-claim-receipt
  allegedIntermediatedPaymentsToWomen
  "Senator Ron Wyden letter dated 2026-03-20, released 2026-03-23, US Senate Finance Committee"
  "https://www.finance.senate.gov/imo/media/doc/senator_wyden_letter_to_leon_black_redacted.pdf ; references EFTA00977823"
  "Wyden characterizes selected emails as raising serious questions about payments through Epstein. The cited redacted email and complete accounts have not been independently reviewed here for this issue; allegation is not a conviction."
  true false false false

wydenSurveillanceQuestion : Wyden2026ClaimReceipt
wydenSurveillanceQuestion = wyden-2026-claim-receipt
  allegedSurveillanceOfWomen
  "US Senate Finance Committee press release 2026-03-23 reporting Wyden letter"
  "https://www.finance.senate.gov/ranking-members-news/continuing-epstein-investigation-wyden-questions-leon-black-over-new-revelations-in-epstein-files-appearance-of-hush-money-payments-and-surveillance-of-women"
  "Wyden's office reports evidence suggesting Epstein and associates surveilled women on Black's behalf. This is a politician's public investigative allegation, requiring source-specific email and conduct checks."
  true false false false

wydenCompensationComparator : Wyden2026ClaimReceipt
wydenCompensationComparator = wyden-2026-claim-receipt
  comparativeProfessionalCompensation
  "Wyden letter dated 2026-03-20, published by Finance Committee 2026-03-23"
  "Letter cites EFTA00621341 Paul Weiss billing and EFTA01915809 wire receipt"
  "Wyden says the stated Epstein fees were far higher than comparable professional advice and questions their rationale. The original amount and comparator scope, not motive, are bounded question objects."
  true false false false

wydenGiftTaxQuestion : Wyden2026ClaimReceipt
wydenGiftTaxQuestion = wyden-2026-claim-receipt
  giftTaxAndCharityQuestions
  "Senate Finance letter 2026-03-20 and public summary 2026-03-23"
  "Letter cites Black-related gift, charitable and trust materials in released DOJ corpus"
  "Senator raises potential mischaracterisation of payments and tax issues, but does not furnish a tax-court ruling or audit conclusion in these public statements."
  true false false false

wydenClaimIsNotAdjudication :
  independentLiabilityOrCriminalVerdictPaid wydenWomenPaymentsQuestion ≡ false
wydenClaimIsNotAdjudication = refl

wydenSurveillanceClaimNotBannonFilmEvidence :
  linksToBannonFilmProgrammePaid wydenSurveillanceQuestion ≡ false
wydenSurveillanceClaimNotBannonFilmEvidence = refl

wydenOriginalMessageStillUninspectedHere :
  sourceUnderlyingItemInspectedForThisClaim wydenWomenPaymentsQuestion ≡ false
wydenOriginalMessageStillUninspectedHere = refl


------------------------------------------------------------------------
-- 2026 HOUSE OVERSIGHT ORIGINAL-OBJECT UPDATE (REPORT 119-831)
--
-- Separate original record of a witness's words, committee's assertions,
-- corporate disclosure, and House procedural disposition.  Neither the
-- record's authenticity nor a vote certifies underlying NDAs or crimes.
-- Formal receipts prove only the explicitly encoded source-state fields.
------------------------------------------------------------------------

data Black2026EvidenceRole : Set where
  witnessInterviewOnRecord : Black2026EvidenceRole
  committeeReportOfItsDispute : Black2026EvidenceRole
  houseProcedureRecorded : Black2026EvidenceRole
  corporateDisclosureOfReview : Black2026EvidenceRole
  independentJudicialDocketEvent : Black2026EvidenceRole

record Black2026SourceReceipt : Set where
  constructor black-2026-source-receipt
  field
    black2026Role : Black2026EvidenceRole
    black2026OriginalLocator : String
    black2026EventDate : String
    black2026PublishedDate : String
    black2026LimitedProposition : String
    black2026OriginalSourceLocated : Bool
    black2026SourceInspected : Bool
    black2026ProvesUnderlyingOffence : Bool
open Black2026SourceReceipt public

blackJuneInterview2026 : Black2026SourceReceipt
blackJuneInterview2026 = black-2026-source-receipt
  witnessInterviewOnRecord
  "House Oversight Leon Black Final Transcript 7.16.26, interview pp 14-15, 28, 41-42; https://oversight.house.gov/wp-content/uploads/2026/07/Leon-Black-Final-Transcript-7.16.26.pdf"
  "2026-06-26" "2026-07-17"
  "Witness confirmed reported terms of a 2015 NDA; described Epstein as informed but not the negotiator; stated separate Dechert conclusions as his account. Neither the agreement nor independent transfer records are enclosed."
  true true false

blackCommitteeReport119831 : Black2026SourceReceipt
blackCommitteeReport119831 = black-2026-source-receipt
  committeeReportOfItsDispute
  "H. Rept. 119-831, 2026-09-15, printed pp 2, 12, 17, 23; https://www.govinfo.gov/content/pkg/CRPT-119hrpt831/pdf/CRPT-119hrpt831.pdf"
  "2026-09-15" "2026-09-15"
  "Committee says one NDA was produced, describes 2015 terms through Black's June witness testimony and advocates referral. The report is not a second independent witness to the 2015 terms."
  true true false

blackHouseResolution1543 : Black2026SourceReceipt
blackHouseResolution1543 = black-2026-source-receipt
  houseProcedureRecorded
  "Congressional Record 2026-09-16 H5931, H. Res. 1543; https://www.govinfo.gov/content/pkg/CREC-2026-09-16/html/CREC-2026-09-16-pt1-PgH5931.htm"
  "2026-09-16" "2026-09-16"
  "House adopted H. Res. 1543 without objection to recommend contempt referral for subpoena compliance; not a DOJ charge, criminal conviction or finding on the contents of any NDA."
  true true false

blackDechertSECOriginal2021 : Black2026SourceReceipt
blackDechertSECOriginal2021 = black-2026-source-receipt
  corporateDisclosureOfReview
  "SEC 2021-01-25 Apollo Form 8-K Exhibit 99.1, Dechert LLP dated 2021-01-22; https://www.sec.gov/Archives/edgar/data/1411494/000119312521016405/d118102dex991.htm"
  "2021-01-22" "2021-01-25"
  "Independent counsel hired by Apollo Conflicts Committee reviewed Black-Epstein personal work; corporate investigative report and witness restatement derive from the same underlying inquiry, not independent forensic examinations."
  true true false

blackApolloProxyConflicts2021 : Black2026SourceReceipt
blackApolloProxyConflicts2021 = black-2026-source-receipt
  corporateDisclosureOfReview
  "Apollo 2021 DEF 14A SEC filing, Conflicts Committee and board disclosures; https://www.sec.gov/Archives/edgar/data/1411494/000119312521247884/d218583ddef14a.htm"
  "2020-2021" "2021-08-18"
  "Apollo identifies Ducey, Krongard and Richards as Conflicts Committee; publicly states Krongard's former senior CIA office. Corporate disclosure establishes historical director-role overlap only, not agency tasking or operational influence in the Dechert review."
  true true false

record Black2026HouseBoundary : Set where
  constructor black-2026-house-boundary
  field
    publicInterviewLocated : Bool
    interview2015TermsWitnessConfirmed : Bool
    interviewEpsteinAwarenessAsserted : Bool
    interviewEpsteinNegotiationProved : Bool
    executed2015NDABytesInspected : Bool
    houseCommitteeReportInspected : Bool
    houseResolutionRecorded : Bool
    missingNDAContentsIndependentlyVerified : Bool
    exactNDAtoBlackPaymentLedgerJoinPaid : Bool
    committeeContemptIsCriminalConviction : Bool
    corporateDirectorPastCIARoleIsCurrentTasking : Bool
    blackCommitteeInquiryJoinsBannonFilm : Bool
    caseWideCovertCommandEstablished : Bool
open Black2026HouseBoundary public

canonicalBlack2026HouseBoundary : Black2026HouseBoundary
canonicalBlack2026HouseBoundary = black-2026-house-boundary
  true true true false false true true false false false false false false

originalHouseTranscriptPaid :
  publicInterviewLocated canonicalBlack2026HouseBoundary ≡ true
originalHouseTranscriptPaid = refl

witnessAwarenessDoesNotEstablishNegotiation :
  interviewEpsteinNegotiationProved canonicalBlack2026HouseBoundary ≡ false
witnessAwarenessDoesNotEstablishNegotiation = refl

signedNDAObjectStillMissing :
  executed2015NDABytesInspected canonicalBlack2026HouseBoundary ≡ false
signedNDAObjectStillMissing = refl

contemptReferralNotConviction :
  committeeContemptIsCriminalConviction canonicalBlack2026HouseBoundary ≡ false
contemptReferralNotConviction = refl

directorPastEmploymentNotTasking :
  corporateDirectorPastCIARoleIsCurrentTasking canonicalBlack2026HouseBoundary ≡ false
directorPastEmploymentNotTasking = refl

black2026HouseDoesNotPayBannonFunding :
  blackCommitteeInquiryJoinsBannonFilm canonicalBlack2026HouseBoundary ≡ false
black2026HouseDoesNotPayBannonFunding = refl

black2026HouseDoesNotPayWholeNetworkH3 :
  caseWideCovertCommandEstablished canonicalBlack2026HouseBoundary ≡ false
black2026HouseDoesNotPayWholeNetworkH3 = refl

------------------------------------------------------------------------
-- OCTOBER 2026 COURT DISPOSITION / SEPTEMBER SUBPOENA CHALLENGE
-- Two distinct federal dockets must never be joined by party surname.
------------------------------------------------------------------------

data Black2026CourtProceeding : Set where
  blackHouseSubpoenaChallengeDDC : Black2026CourtProceeding
  separateDoeBlackCivilActionSDNY : Black2026CourtProceeding

blackDoeNotHouseChallenge :
  separateDoeBlackCivilActionSDNY ≡ blackHouseSubpoenaChallengeDDC → ⊥
blackDoeNotHouseChallenge ()

blackHouseSubpoenaChallengeDocket : Black2026SourceReceipt
blackHouseSubpoenaChallengeDocket = black-2026-source-receipt
  independentJudicialDocketEvent
  "Black v House Committee on Oversight et al, DDC 1:26-cv-03084, docket and complaint filed 2026-09-03; https://dockets.justia.com/docket/district-of-columbia/dcdce/1:2026cv03084/296175"
  "2026-09-03" "2026-09-03"
  "The docket listing authenticates existence of the civil subpoena challenge and complaint. The publicly retrieved docket listing was last refreshed 2026-09-03; later judgment or dismissal is not confirmed here."
  true true false

blackDoeOctoberDismissalOriginalOrder : Black2026SourceReceipt
blackDoeOctoberDismissalOriginalOrder = black-2026-source-receipt
  independentJudicialDocketEvent
  "Doe v Black, SDNY 23-cv-6418 (JGLC), 2026-10-15 ECF 485; https://cases.justia.com/federal/district-courts/new-york/nysdce/1:2023cv06418/602764/485/0.pdf"
  "2026-10-15" "2026-10-15"
  "Judge Clarke granted plaintiff-requested voluntary dismissal with prejudice under Fed. R. Civ. P. 41(a)(2), with defendant not opposing; court reserved ECF 440 fees motion. This is NOT a merits adjudication of the underlying allegations and does not dispose the separate DDC House subpoena action."
  true true false

record Black2026DistinctCourtCaseBoundary : Set where
  constructor black-2026-distinct-court-case-boundary
  field
    sdnyDismissalOrderInspected : Bool
    plaintiffRequestedDismissal : Bool
    defendantDidNotOpposeDismissal : Bool
    sdnyDismissalIsTrialFactFinding : Bool
    sdnyCourtResolvedFeesMotion : Bool
    ddcComplaintDocketIdentified : Bool
    ddcFinalDispositionIndependentlyVerified : Bool
    sdnyOrderAdjudicatesHouseSubpoenaCase : Bool
open Black2026DistinctCourtCaseBoundary public

canonicalBlack2026DistinctCourtCaseBoundary : Black2026DistinctCourtCaseBoundary
canonicalBlack2026DistinctCourtCaseBoundary = black-2026-distinct-court-case-boundary
  true true true false false true false false

voluntaryDismissalNotTrialFinding :
  sdnyDismissalIsTrialFactFinding canonicalBlack2026DistinctCourtCaseBoundary ≡ false
voluntaryDismissalNotTrialFinding = refl

feesMotionNotResolvedByDismissal :
  sdnyCourtResolvedFeesMotion canonicalBlack2026DistinctCourtCaseBoundary ≡ false
feesMotionNotResolvedByDismissal = refl

separateDocketNotResolvedByDoeDismissal :
  sdnyOrderAdjudicatesHouseSubpoenaCase canonicalBlack2026DistinctCourtCaseBoundary ≡ false
separateDocketNotResolvedByDoeDismissal = refl

ddcFinalDispositionStillUnverified :
  ddcFinalDispositionIndependentlyVerified canonicalBlack2026DistinctCourtCaseBoundary ≡ false
ddcFinalDispositionStillUnverified = refl
