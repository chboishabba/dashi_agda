{-# OPTIONS --safe #-}
module DASHI.Law.SensibLawWoogarooSpringfieldStatutoryInfrastructureGate20261030Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawWoogarooDeveloperGasTemporalIdentityCut20261030Exact as Developer
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Lobby
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Ibrahim
import DASHI.Wikimedia.IdentifierExact as Identifier
import DASHI.Law.SensibLawWoogaroo9281QueenslandCommencementEnforcementCutExact as LocalWorks

------------------------------------------------------------------------
-- SPRINGFIELD PLANNING ACT ss 275T-275ZA (2024)
--
-- SOURCE-POSITIVE legal process, NOT another free-floating influence graph:
-- 275T expressly defines SCG as Springfield City Group Pty Limited,
-- ACN 055 714 531. For a non-SCG plan application, 275X/Y require
-- notice, disclosure to SCG and applicant response to timely submissions.
-- 275Z calls for a statement covering area effects, infrastructure
-- servicing and remedies. Council must have regard to that statement;
-- 275Z(3) explicitly prevents non-compliance alone stopping decision.
-- 275W separately restricts approval to specified infrastructure routes.
--
-- The indexed 6243/2023/LAP s275Z comment proves a DOCUMENT TITLE ONLY.
-- Its letter, contents, timing, applicable agreement, actual satisfaction,
-- gas provision and any response/approval reasoning are NOT acquired.
-- A statutory review right is neither a 2025 lobbying instruction nor a
-- Commonwealth EPBC 2019/8575 approval role.
------------------------------------------------------------------------

queenslandPlanningAct2024 : Source.AttributedSource
queenslandPlanningAct2024 = Source.mkNoDOISource
  "Queensland Parliament"
  "Planning Act 2016, Chapter 7 Part 4C, sections 275T-275ZA"
  "Queensland legislation, in-force 6 June 2024 (provisions enacted 2020)"
  "6 June 2024"
  "https://www.legislation.qld.gov.au/view/whole/html/inforce/2024-06-06/act-2016-025"
  Source.governmentSource
  "Original statute defines SCG by ACN; 275V owner consent; 275W infrastructure threshold; 275X/Y notice and materials; 275Z statement on adverse impact, servicing and options plus council regard and no automatic decision bar; 275ZAA Urban Utilities representation; 275ZA decision notice. Does not name a gas servicing contract or prove particular case compliance."
  Source.publicAttribution

councilSpringviewIndex : Source.AttributedSource
councilSpringviewIndex = Developer.springfieldCityGroupCouncilCommentIndex2024

statutorySourceAtlas : Source.AttributedSourceAtlas
statutorySourceAtlas = Source.mkSourceAtlas
  "Springfield statutory planning and infrastructure statement route"
  "DASHI.Law.SensibLawWoogarooSpringfieldStatutoryInfrastructureGate20261030Exact"
  (queenslandPlanningAct2024 ∷ councilSpringviewIndex ∷ [])
  "Statute and the Council index are distinct original producers. No signed comment document or agreement imported."

-- A dated, literal corporate ID, not a guessed QID or title inference.
scgACN : String
scgACN = "055714531"

data ParticipationRole : Set where
  statutorySCGRecipientAndCommenter : ParticipationRole
  stateRegisteredLobbyistContact : ParticipationRole

roleDistinct :
  statutorySCGRecipientAndCommenter ≡ stateRegisteredLobbyistContact → ⊥
roleDistinct ()

data RequiredSection : Set where
  s275V : RequiredSection
  s275W : RequiredSection
  s275X : RequiredSection
  s275Y : RequiredSection
  s275Z : RequiredSection
  s275ZAA : RequiredSection
  s275ZA : RequiredSection

data StatutoryFunction : Set where
  ownerConsentOrException : StatutoryFunction
  infrastructureServicingSatisfaction : StatutoryFunction
  preApplicationNoticeToSCG : StatutoryFunction
  disclosureAndResponsesToSCG : StatutoryFunction
  scgWrittenStatement : StatutoryFunction
  urbanUtilitiesRepresentations : StatutoryFunction
  noticeOfDecision : StatutoryFunction

sectionFunction : RequiredSection → StatutoryFunction
sectionFunction s275V = ownerConsentOrException
sectionFunction s275W = infrastructureServicingSatisfaction
sectionFunction s275X = preApplicationNoticeToSCG
sectionFunction s275Y = disclosureAndResponsesToSCG
sectionFunction s275Z = scgWrittenStatement
sectionFunction s275ZAA = urbanUtilitiesRepresentations
sectionFunction s275ZA = noticeOfDecision

-- The statutory roles themselves are source-described. Their satisfaction
-- in any particular Council case is an independent empirical/legal question.
data Section275ZTopic : Set where
  adverseStructurePlanImpact : Section275ZTopic
  agreementIndexedInfrastructureServicing : Section275ZTopic
  optionsToAddressEitherIssue : Section275ZTopic

section275ZRequiredTopics : List Section275ZTopic
section275ZRequiredTopics =
  adverseStructurePlanImpact ∷
  agreementIndexedInfrastructureServicing ∷
  optionsToAddressEitherIssue ∷ []

section275ZContainsInfrastructureSlot :
  section275ZRequiredTopics ≡
  (adverseStructurePlanImpact ∷ agreementIndexedInfrastructureServicing ∷
   optionsToAddressEitherIssue ∷ [])
section275ZContainsInfrastructureSlot = refl

data InfrastructureApprovalAlternative : Set where
  agreementServicingPresent : InfrastructureApprovalAlternative
  agreementServicingExpected : InfrastructureApprovalAlternative
  consistentInterimServicingPresent : InfrastructureApprovalAlternative
  consistentInterimServicingExpected : InfrastructureApprovalAlternative

data EvidenceSlot : Set where
  planApplicationNonSCGStatus : EvidenceSlot
  section275XPrelodgementService : EvidenceSlot
  section275YPlanAndAmendments : EvidenceSlot
  actual275ZStatementFace : EvidenceSlot
  councilAssessmentAndRegard : EvidenceSlot
  currentInfrastructureAgreementFace : EvidenceSlot
  infrastructureCategoryAndScope : EvidenceSlot
  applicableParcelAndAssets : EvidenceSlot
  specificGasReticulationContract : EvidenceSlot
  lobbyMeeting2025ActualSubject : EvidenceSlot
  commonwealth20198575DecisionFile : EvidenceSlot

record IndexedCasePayment : Set where
  constructor indexed-case-payment
  field
    applicationId : String
    index : Source.AttributedSource
    scgCommentDocumentIndexed : Bool
    signedCommentFacePaid : Bool
    nonSCGQualificationIndependentlyPaid : Bool
    specificInfrastructureAgreementPaid : Bool
    gasTopicPaid : Bool

springviewIndexState : IndexedCasePayment
springviewIndexState = indexed-case-payment
  "6243/2023/LAP"
  councilSpringviewIndex
  true false false false false

-- The Council's statutory satisfaction may occur under different serviced
-- infrastructure schedules.  Section 275W does not itself specify gas.
data ServicingWorld : Set where
  nonGasAgreementOnly : ServicingWorld
  agreementAlsoSpecifiesGas : ServicingWorld

data StatutorySatisfactionObservation : Set where
  listedInfrastructurePathSufficient : StatutorySatisfactionObservation

data GasInAgreement : Set where
  gasNotEstablished : GasInAgreement
  gasSpecificallyDocumented : GasInAgreement

observedInfrastructure : ServicingWorld → StatutorySatisfactionObservation
observedInfrastructure nonGasAgreementOnly = listedInfrastructurePathSufficient
observedInfrastructure agreementAlsoSpecifiesGas = listedInfrastructurePathSufficient

gasScope : ServicingWorld → GasInAgreement
gasScope nonGasAgreementOnly = gasNotEstablished
gasScope agreementAlsoSpecifiesGas = gasSpecificallyDocumented

differentGasScope :
  gasScope nonGasAgreementOnly ≡ gasScope agreementAlsoSpecifiesGas → ⊥
differentGasScope ()

statutoryInfrastructurePathDoesNotProveGas :
  INF.FactorsThrough observedInfrastructure gasScope → ⊥
statutoryInfrastructurePathDoesNotProveGas =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness nonGasAgreementOnly
      agreementAlsoSpecifiesGas refl differentGasScope)

-- SCG's statutory locus is a positive role in a local plan process;
-- the same observed statutory locus is compatible with either outcome
-- of a wholly separate 2025 Queensland lobbyist meeting.
data LobbyWorld : Set where
  statutoryRoleNoGasLobbyRequest : LobbyWorld
  statutoryRoleWithSeparatelyPaidGasRequest : LobbyWorld

data StatutoryRoleObserved : Set where
  namedSCGRightsInPlanningAct : StatutoryRoleObserved

data LobbySubjectRecord : Set where
  actualGasSubjectUnpaid : LobbySubjectRecord
  actualGasSubjectPaid : LobbySubjectRecord

statutoryRole : LobbyWorld → StatutoryRoleObserved
statutoryRole statutoryRoleNoGasLobbyRequest = namedSCGRightsInPlanningAct
statutoryRole statutoryRoleWithSeparatelyPaidGasRequest = namedSCGRightsInPlanningAct

lobbySubject : LobbyWorld → LobbySubjectRecord
lobbySubject statutoryRoleNoGasLobbyRequest = actualGasSubjectUnpaid
lobbySubject statutoryRoleWithSeparatelyPaidGasRequest = actualGasSubjectPaid

distinctLobbySubject :
  lobbySubject statutoryRoleNoGasLobbyRequest ≡
  lobbySubject statutoryRoleWithSeparatelyPaidGasRequest → ⊥
distinctLobbySubject ()

statutoryRoleDoesNotDetermineSantoroRequest :
  INF.FactorsThrough statutoryRole lobbySubject → ⊥
statutoryRoleDoesNotDetermineSantoroRequest =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness statutoryRoleNoGasLobbyRequest
      statutoryRoleWithSeparatelyPaidGasRequest refl distinctLobbySubject)

------------------------------------------------------------------------
-- ACTUAL ORIGINAL INFRASTRUCTURE AGREEMENT / 2018 COURT HISTORY
------------------------------------------------------------------------

springfieldStructurePlan2025 : Source.AttributedSource
springfieldStructurePlan2025 = Source.mkNoDOISource
  "Ipswich City Council"
  "Springfield Structure Plan, Ipswich City Plan 2025, section 1.7 p 4 and section 4 p 1"
  "Council-published Springfield Structure Plan original PDF"
  "2025"
  "https://hdp-au-prod-app-ipsw-shapeyouripswich-files.s3.ap-southeast-2.amazonaws.com/9417/5607/4591/Springfield_Structure_Plan.pdf"
  Source.governmentSource
  "Council original expressly records Springfield Infrastructure Agreement 1998 entered by Council, Springfield Land Corporation Pty Ltd, Springfield Land Corporation (No.2) Pty Ltd and Cherish Enterprises Pty Ltd; deals with roads, water, sewer, drainage, open space, community facilities, development phasing. Distinct Town Centre agreement 2015. Source is the 2025 plan statement, not signed 1998 agreement or project-specific gas contract."
  Source.publicAttribution

qca266OfficialCarrier : Source.AttributedSource
qca266OfficialCarrier = Source.mkNoDOISource
  "Supreme Court of Queensland, Court of Appeal: Fraser and Gotterson JJA and Burns J"
  "Springfield Land Corporation Pty Limited v Cherish Enterprises Pty Ltd and Ipswich City Council [2018] QCA 266"
  "Official Queensland Judgments reporter with original QCA court reasons"
  "12 October 2018"
  "https://www.queenslandjudgments.com.au/caselaw/qca/2018/266"
  (Source.namedSourceKind "court judgment")
  "Court of Appeal file 8535 of 2017, P&E Appeal 2948 of 2016; declaration that area development plan approval was necessary before assessment/approval of Cherish's application made about 17 March 2016; recorded 1998 infrastructure agreement and its parties. Original court judgment text is now independently accessible in the official Queensland Judgments reporter. Not a 2026 EPBC holding."
  Source.publicAttribution

record HistoricAgreement : Set where
  constructor historic-agreement
  field
    source : Source.AttributedSource
    namedCouncilAndCherishParties : Bool
    originalAgreementSignedFaceAcquired : Bool
    specific20198575AgreementApplied : Bool
    gasIncludedInAgreementEstablished : Bool
open HistoricAgreement public

springfield1998OriginalAgreementLocator : HistoricAgreement
springfield1998OriginalAgreementLocator = historic-agreement
  springfieldStructurePlan2025
  true false false false

data HistoricalJudicialScope : Set where
  cherish2016PlanningApplication : HistoricalJudicialScope
  federal20198575Approval : HistoricalJudicialScope

record OriginalJudgmentState : Set where
  constructor original-judgment-state
  field
    source : Source.AttributedSource
    determinedCase : HistoricalJudicialScope
    judgmentDelivered : Bool
    federal2026BreachJudged : Bool
open OriginalJudgmentState public

qca266PriorJudgment : OriginalJudgmentState
qca266PriorJudgment = original-judgment-state
  qca266OfficialCarrier cherish2016PlanningApplication true false

historicalCaseNotPresentEPBCAction :
  cherish2016PlanningApplication ≡ federal20198575Approval → ⊥
historicalCaseNotPresentEPBCAction ()

-- Planning agreement duties concern particular premises and effective terms.
-- A recorded 1998 agreement does not identify later per-lot burdens, and the
-- Council's own 2021 consultation reports a clause 229 residential lot
-- successor-release provision requiring exact contract/title reconciliation.
data AgreementIncidenceWorld : Set where
  agreementBurdenPreservedForParcel : AgreementIncidenceWorld
  residentialLotReleasedFromBurden : AgreementIncidenceWorld

data HistoricAgreementObserved : Set where
  councilNames1998Agreement : HistoricAgreementObserved

data ParcelObligationStatus : Set where
  successorBurdenProved : ParcelObligationStatus
  successorBurdenNotProved : ParcelObligationStatus

agreementObserved : AgreementIncidenceWorld → HistoricAgreementObserved
agreementObserved agreementBurdenPreservedForParcel = councilNames1998Agreement
agreementObserved residentialLotReleasedFromBurden = councilNames1998Agreement

parcelObligation : AgreementIncidenceWorld → ParcelObligationStatus
parcelObligation agreementBurdenPreservedForParcel = successorBurdenProved
parcelObligation residentialLotReleasedFromBurden = successorBurdenNotProved

differentParcelObligation :
  parcelObligation agreementBurdenPreservedForParcel ≡
  parcelObligation residentialLotReleasedFromBurden → ⊥
differentParcelObligation ()

historicalSIAAloneDoesNotPaySuccessorBurden :
  INF.FactorsThrough agreementObserved parcelObligation → ⊥
historicalSIAAloneDoesNotPaySuccessorBurden =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness agreementBurdenPreservedForParcel
      residentialLotReleasedFromBurden refl differentParcelObligation)

data IndexedDocketFace : Set where
  scgReferral29June2023 : IndexedDocketFace
  scgResponse14March2024 : IndexedDocketFace
  councilDecision21March2024 : IndexedDocketFace
  cherishLandownerConsent29June2023 : IndexedDocketFace
  stocklandSubmissionConsent29June2023 : IndexedDocketFace

council6243DocumentSequence : List IndexedDocketFace
council6243DocumentSequence =
  scgReferral29June2023 ∷
  cherishLandownerConsent29June2023 ∷
  stocklandSubmissionConsent29June2023 ∷
  scgResponse14March2024 ∷
  councilDecision21March2024 ∷ []

-- These are INDEXED original documents, not independently inspected faces.
-- SCG's 275Z clock may restart after new 275Y(3) materials: do not assume
-- late reply by subtracting March 2024 from the June 2023 application date.
data TimingWorld : Set where
  responseToLaterInformationRequest : TimingWorld
  responseWithoutKnownTriggerReceipt : TimingWorld

data SameIndexDates : Set where
  JuneAndMarchIndexDates : SameIndexDates

data TenBusinessDayCompliance : Set where
  complianceUnassessed : TenBusinessDayCompliance
  triggeredTimelinessDocumented : TenBusinessDayCompliance

indexDates : TimingWorld → SameIndexDates
indexDates responseToLaterInformationRequest = JuneAndMarchIndexDates
indexDates responseWithoutKnownTriggerReceipt = JuneAndMarchIndexDates

timingProof : TimingWorld → TenBusinessDayCompliance
timingProof responseToLaterInformationRequest = triggeredTimelinessDocumented
timingProof responseWithoutKnownTriggerReceipt = complianceUnassessed

distinctTiming :
  timingProof responseToLaterInformationRequest ≡
  timingProof responseWithoutKnownTriggerReceipt → ⊥
distinctTiming ()

indexDatesDoNotProveLateStatement :
  INF.FactorsThrough indexDates timingProof → ⊥
indexDatesDoNotProveLateStatement =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness responseToLaterInformationRequest
      responseWithoutKnownTriggerReceipt refl distinctTiming)

------------------------------------------------------------------------
-- EXACT IDENTIFIER / PRODUCER / STATUTORY ROLE ALIGNMENT
------------------------------------------------------------------------

-- The 2018 original court caption names Springfield Land Corporation
-- Pty Limited ACN 055714531; the 2024 Act names Springfield City Group
-- Pty Limited ACN 055714531. Same number, different dated public names.
-- This is not a certificate establishing a particular ASIC rename date.
historicalCourtPartyACN : String
historicalCourtPartyACN = "055714531"

historicalCourtAndPresentSCGACNMatch :
  historicalCourtPartyACN ≡ scgACN
historicalCourtAndPresentSCGACNMatch = refl

data CouncilNamedService : Set where
  roads : CouncilNamedService
  waterSupply : CouncilNamedService
  sewerage : CouncilNamedService
  stormwaterDrainage : CouncilNamedService
  openSpace : CouncilNamedService
  communityFacilities : CouncilNamedService
  electricityAndTelephone : CouncilNamedService

-- Source: Council Springfield Structure Plan section 1.7 and section 4.
-- Not an exhaustive inventory of executed 1998 deed schedules.
publishedPlanServiceList : List CouncilNamedService
publishedPlanServiceList =
  roads ∷ waterSupply ∷ sewerage ∷ stormwaterDrainage ∷
  openSpace ∷ communityFacilities ∷ electricityAndTelephone ∷ []

-- Reuse prior Ibrahim original named public-law QID as navigation ONLY,
-- never mint one for the SCG legal person, Cherish or an unseen agreement.
environmentalLawNavigationQid : Identifier.ItemId
environmentalLawNavigationQid = Ibrahim.environmentalLawQid

-- The 2024 s275Z text and Council index can motivate an infrastructure
-- contract search without upgrading to an executed gas service or payment.
data CommercialJoin : Set where
  agreementIdentityAndParcel : CommercialJoin
  specificUtilityScope : CommercialJoin
  contractingPartiesAndConsideration : CommercialJoin
  successorAndSubdivisionTerms : CommercialJoin
  observedPhysicalAssetOrMeter : CommercialJoin
  actualIncomeAndBeneficiary : CommercialJoin

priorityCommercialJoins : List CommercialJoin
priorityCommercialJoins =
  agreementIdentityAndParcel ∷ specificUtilityScope ∷
  contractingPartiesAndConsideration ∷ successorAndSubdivisionTerms ∷
  observedPhysicalAssetOrMeter ∷ actualIncomeAndBeneficiary ∷ []


------------------------------------------------------------------------
-- RELATION-TYPED HISTORY: CONTRACT, ADVERSARIAL CASE, STATUTORY REVIEW
-- These are three different paths, not one friendly ownership edge.
------------------------------------------------------------------------

data RelationshipKind : Set where
  contractualHistoricalInfrastructureParticipant : RelationshipKind
  adversarialPlanningLitigation : RelationshipKind
  statutoryNonApplicantReview : RelationshipKind
  recordedLobbyingAccess : RelationshipKind

record RelationshipReceipt : Set where
  constructor relationship-receipt
  field
    kind : RelationshipKind
    source : Source.AttributedSource
    temporalKey : String
    paidDocumentContent : Bool
    provesFinancialTransfer : Bool
    provesGasLobbying : Bool

open RelationshipReceipt public

councilCherish1998ContractContext : RelationshipReceipt
councilCherish1998ContractContext = relationship-receipt
  contractualHistoricalInfrastructureParticipant
  springfieldStructurePlan2025
  "Springfield Infrastructure Agreement 1998; original Council plan description"
  true false false

cherishSCGAdversarialAppeal2018 : RelationshipReceipt
cherishSCGAdversarialAppeal2018 = relationship-receipt
  adversarialPlanningLitigation
  qca266OfficialCarrier
  "[2018] QCA 266; Court of Appeal 8535/2017; 12 Oct 2018"
  true false false

scgCommentStatutoryRoute2024 : RelationshipReceipt
scgCommentStatutoryRoute2024 = relationship-receipt
  statutoryNonApplicantReview
  councilSpringviewIndex
  "6243/2023/LAP; s275Z entry 6; 14 Mar 2024"
  false false false

santoroAccessDistinctFromStatutoryRole : RelationshipReceipt
santoroAccessDistinctFromStatutoryRole = relationship-receipt
  recordedLobbyingAccess
  Developer.april2025Diary
  "9 Apr 2025 Treasurer/Energy portfolio office"
  true false false

relationshipHistory : List RelationshipReceipt
relationshipHistory =
  councilCherish1998ContractContext ∷
  cherishSCGAdversarialAppeal2018 ∷
  scgCommentStatutoryRoute2024 ∷
  santoroAccessDistinctFromStatutoryRole ∷ []

-- A recorded historical agreement does not turn earlier adversarial
-- litigation into an agreed current revenue-sharing scheme.
data RelationshipWorld : Set where
  oldDealAndCourtNoCurrentCashflow : RelationshipWorld
  oldDealAndCourtSeparatelyPaidCurrentCashflow : RelationshipWorld

data ObservedHistory : Set where
  agreementAndAppealExist : ObservedHistory

data CurrentCommercialGain : Set where
  currentGainNotDocumented : CurrentCommercialGain
  currentGainDocumented : CurrentCommercialGain

history : RelationshipWorld → ObservedHistory
history oldDealAndCourtNoCurrentCashflow = agreementAndAppealExist
history oldDealAndCourtSeparatelyPaidCurrentCashflow = agreementAndAppealExist

gain : RelationshipWorld → CurrentCommercialGain
gain oldDealAndCourtNoCurrentCashflow = currentGainNotDocumented
gain oldDealAndCourtSeparatelyPaidCurrentCashflow = currentGainDocumented

gainDifference :
  gain oldDealAndCourtNoCurrentCashflow ≡
  gain oldDealAndCourtSeparatelyPaidCurrentCashflow → ⊥
gainDifference ()

agreementAndAdversarialJudgmentDoNotDetermineCurrentBenefit :
  INF.FactorsThrough history gain → ⊥
agreementAndAdversarialJudgmentDoNotDetermineCurrentBenefit =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness oldDealAndCourtNoCurrentCashflow
      oldDealAndCourtSeparatelyPaidCurrentCashflow refl gainDifference)

------------------------------------------------------------------------
-- STATE COMMENCEMENT WELD: reused 9281/2024/OW authority, no new scheme.
------------------------------------------------------------------------

-- Section 275ZB structures Springfield plan prerequisites and exceptions.
-- The distinct 9281 local works owner already carries s72, s164, s180
-- and literal condition 6(a).  These are two state legal consumers, not
-- self-paying proofs of site-works commencement or an offence.
existingLocalStatePreservationCut : LocalWorks.QueenslandPreservationCut
existingLocalStatePreservationCut = LocalWorks.canonicalQueenslandPreservationCut

existingLocalStatePrestartCut : LocalWorks.QueenslandCutPareto
existingLocalStatePrestartCut = LocalWorks.canonicalQueenslandCutPareto

data StartWorksCoordinate : Set where
  springfieldPlanHierarchyS275ZB : StartWorksCoordinate
  councilOperationalWorks9281Condition6a : StartWorksCoordinate
  planningActS72Prestart : StartWorksCoordinate
  planningActS164Offence : StartWorksCoordinate
  planningActS180Enforcement : StartWorksCoordinate
  federalEPBC20198575Instrument : StartWorksCoordinate

localStartWorksAcquisitionOrder : List StartWorksCoordinate
localStartWorksAcquisitionOrder =
  springfieldPlanHierarchyS275ZB ∷
  councilOperationalWorks9281Condition6a ∷
  planningActS72Prestart ∷
  planningActS164Offence ∷
  planningActS180Enforcement ∷
  federalEPBC20198575Instrument ∷ []

record SamePhaseLocalPayment : Set where
  constructor same-phase-local-payment
  field
    originalPlanHierarchyPaid : Bool
    literal9281Condition6aSubmittedInstrumentPaid : Bool
    sameParcelAndWorksPhasePaid : Bool
    physicalClearingEvidencePaid : Bool
    planningActOffenceEstablished : Bool

samePhaseLocalResidual : SamePhaseLocalPayment
samePhaseLocalResidual = same-phase-local-payment
  false false false false false

------------------------------------------------------------------------
-- 2016-2024 SPRINGFIELD PRIMARY JUDGMENT LINEAGE AND CONTRACT-EXHIBIT CUT
-- The real SIA remains unacquired, but the judge records the appeal book
-- exact pages: AB628-903 for 1998 SIA and AB904-942 for amendment deeds.
------------------------------------------------------------------------

cherish2017QPECOriginalCourt : Source.AttributedSource
cherish2017QPECOriginalCourt = Source.mkNoDOISource
  "Planning and Environment Court of Queensland, Kefford DCJ"
  "Cherish Enterprises Pty Ltd v Ipswich City Council [2017] QPEC 38"
  "Official Queensland Judgments litigation-history and court case record"
  "14 July 2017"
  "https://www.queenslandjudgments.com.au/caselaw/qpec/2017/38"
  (Source.namedSourceKind "court judgment")
  "Initial declaration favoured Cherish's March 2016 development application without prior ADP/precinct plans, but was SET ASIDE by Court of Appeal in [2018] QCA 266. Do not cite the 2017 declaration as governing law or a 2026 EPBC outcome."
  Source.publicAttribution

springLake2023QCAOriginalCourt : Source.AttributedSource
springLake2023QCAOriginalCourt = Source.mkNoDOISource
  "Supreme Court of Queensland Court of Appeal, Morrison, Dalton and Boddice JJA"
  "Spring Lake Holdings Pty Ltd v Ipswich City Council [2023] QCA 233"
  "Original Queensland Judgments court reasons, appeal 2994/2023 from QPEC 1428/2021"
  "24 November 2023"
  "https://www.queenslandjudgments.com.au/caselaw/qca/2023/233"
  (Source.namedSourceKind "court judgment")
  "Distinct Spring Lake Holdings applicant ACN 156492885 and separate parcel/proceeding. Court dismissed application for leave from jurisdictional finding concerning ADP modification. Cites 2018 QCA 266 but does not decide the 6243/2023/LAP consent or EPBC 2019/8575 merits."
  Source.publicAttribution

springLake2024HighCourtDisposition : Source.AttributedSource
springLake2024HighCourtDisposition = Source.mkNoDOISource
  "High Court of Australia, Gageler CJ and six Justices"
  "Spring Lake Holdings Pty Ltd v Ipswich City Council [2024] HCASL 92"
  "Original High Court special-leave disposition, file B71/2023"
  "11 April 2024"
  "https://www.hcourt.gov.au/sites/default/files/eresources/2024/HCASL/92.pdf"
  (Source.namedSourceKind "High Court special-leave disposition")
  "Special leave to appeal from [2023] QCA 233 refused with costs. Not a High Court merits decision endorsing every lower-court proposition, not a new precedent made in 2026, and not a 2019/8575 case."
  Source.publicAttribution

data JudicialTier : Set where
  trialDeclarationSetAside : JudicialTier
  appealsMeritsDetermined : JudicialTier
  otherPartyLeaveDismissed : JudicialTier
  specialLeaveDeniedNotMerits : JudicialTier

record HistoricalCaseReceipt : Set where
  constructor historical-case-receipt
  field
    exactCitation : String
    caseSource : Source.AttributedSource
    judgmentTier : JudicialTier
    is20198575FederalProceeding : Bool
    operativeOnOriginalPartyAndApplication : Bool

cherish2017TrialState : HistoricalCaseReceipt
cherish2017TrialState = historical-case-receipt
  "[2017] QPEC 38"
  cherish2017QPECOriginalCourt
  trialDeclarationSetAside
  false false

cherish2018AppealState : HistoricalCaseReceipt
cherish2018AppealState = historical-case-receipt
  "[2018] QCA 266"
  qca266OfficialCarrier
  appealsMeritsDetermined
  false true

springLake2023AppealState : HistoricalCaseReceipt
springLake2023AppealState = historical-case-receipt
  "[2023] QCA 233"
  springLake2023QCAOriginalCourt
  otherPartyLeaveDismissed
  false false

springLake2024HighCourtState : HistoricalCaseReceipt
springLake2024HighCourtState = historical-case-receipt
  "[2024] HCASL 92"
  springLake2024HighCourtDisposition
  specialLeaveDeniedNotMerits
  false false

data HistoricCourtRecordItem : Set where
  courtAppealBook1998SIA : HistoricCourtRecordItem
  courtAppealBook1998DeedAmendments : HistoricCourtRecordItem
  historic2016ADPApplication : HistoricCourtRecordItem
  current2026SameLotTitleAndContract : HistoricCourtRecordItem

record CourtExhibitLocator : Set where
  constructor court-exhibit-locator
  field
    object : HistoricCourtRecordItem
    source : Source.AttributedSource
    originalPages : String
    quotedCourtFindingPaid : Bool
    completeSignedContractFaceReceived : Bool

appealBook1998Contract : CourtExhibitLocator
appealBook1998Contract = court-exhibit-locator
  courtAppealBook1998SIA qca266OfficialCarrier
  "QCA 266 [17] note 19: appeal book AB628-903, original SIA"
  true false

appealBook1998Amendments : CourtExhibitLocator
appealBook1998Amendments = court-exhibit-locator
  courtAppealBook1998DeedAmendments qca266OfficialCarrier
  "QCA 266 [17] note 19: appeal book AB904-942, deed amendments"
  true false

-- A case citation that establishes parties and prior land is not itself a
-- signed deed, nor a finding that its duties attach to each present lot.
data AppealBookWorld : Set where
  agreementJudiciallyReferencedWithoutExecutionFile : AppealBookWorld
  agreementJudiciallyReferencedWithCompleteFile : AppealBookWorld

data SameCourtReference : Set where
  appealBookPagesJudiciallyIdentified : SameCourtReference

data ExactExecutedAgreementEvidence : Set where
  executedAgreementNotReceived : ExactExecutedAgreementEvidence
  executedAgreementNowReceived : ExactExecutedAgreementEvidence

courtCitation : AppealBookWorld → SameCourtReference
courtCitation agreementJudiciallyReferencedWithoutExecutionFile = appealBookPagesJudiciallyIdentified
courtCitation agreementJudiciallyReferencedWithCompleteFile = appealBookPagesJudiciallyIdentified

executedAgreementFace : AppealBookWorld → ExactExecutedAgreementEvidence
executedAgreementFace agreementJudiciallyReferencedWithoutExecutionFile = executedAgreementNotReceived
executedAgreementFace agreementJudiciallyReferencedWithCompleteFile = executedAgreementNowReceived

differentSignedFace :
  executedAgreementFace agreementJudiciallyReferencedWithoutExecutionFile ≡
  executedAgreementFace agreementJudiciallyReferencedWithCompleteFile → ⊥
differentSignedFace ()

judiciallyIdentifiedAppealPagesDoNotSupplyExecutedDeed :
  INF.FactorsThrough courtCitation executedAgreementFace → ⊥
judiciallyIdentifiedAppealPagesDoNotSupplyExecutedDeed =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness agreementJudiciallyReferencedWithoutExecutionFile
      agreementJudiciallyReferencedWithCompleteFile refl differentSignedFace)

-- A refusal of High Court special leave is an ACTUAL court disposition,
-- not a High Court judgment determining merits of the Springfield ADP rules.
data DispositionKind : Set where
  appellateMeritsDetermination : DispositionKind
  discretionarySpecialLeaveRefusal : DispositionKind

dispositionsAreDifferent :
  appellateMeritsDetermination ≡ discretionarySpecialLeaveRefusal → ⊥
dispositionsAreDifferent ()


------------------------------------------------------------------------
-- NEWLY INSPECTED OFFICIAL [2017] QPEC 38 ORIGINAL PDF PP 29-31
-- Paragraph [73] RECITES specific 1998 Springfield Infrastructure Agreement
-- provisions from an agreed court exhibit, NOT a complete executed deed.
-- The trial judge's later DECLARATION was set aside by [2018] QCA 266.
-- Contract clause recitals remain historical source-specific data only.
------------------------------------------------------------------------

cherish2017OriginalReasonsPDF : Source.AttributedSource
cherish2017OriginalReasonsPDF = Source.mkNoDOISource
  "Planning and Environment Court of Queensland, Kefford DCJ"
  "Cherish Enterprises Pty Ltd v Ipswich City Council [2017] QPEC 38, reasons paragraph [73]"
  "Official original judgment PDF, court-reported 1998 SIA terms, pages 29-31"
  "14 July 2017"
  "https://www.queenslandjudgments.com.au/caselaw/qpec/2017/38/pdf"
  (Source.namedSourceKind "court judgment")
  "Original judgment PDF p29-31 [73] summarises 1998 SIA clauses 14,19,22,132,134,190,192,215,274 from agreed exhibits. Underlying deed and amendments not received. The 2017 development-entitlement declaration was SET ASIDE by [2018] QCA 266; recital is not a new 2026 rights or actual-financial-transfer determination."
  Source.publicAttribution

data SIA1998ClauseMechanism : Set where
  severanceAndSubstituteNegotiation : SIA1998ClauseMechanism
  areaDevelopmentPlanAgreementPriority : SIA1998ClauseMechanism
  conditionalEntitlementChangeReimbursement : SIA1998ClauseMechanism
  openSpaceMasterPlanConsistency : SIA1998ClauseMechanism
  drainageMasterPlanConsistency : SIA1998ClauseMechanism
  councilMayConditionInfrastructurePerformance : SIA1998ClauseMechanism
  subdivisionSurveySealingPrerequisites : SIA1998ClauseMechanism

record CourtReportedClause : Set where
  constructor court-reported-clause
  field
    originalCourtCarrier : Source.AttributedSource
    clauseNumber : String
    courtParagraph : String
    legalMechanism : SIA1998ClauseMechanism
    fullOriginalSignedDeedPaid : Bool
    present2026SameLotApplicationProved : Bool
    actualPaymentOrBreachEstablished : Bool

sIAClause22Reported : CourtReportedClause
sIAClause22Reported = court-reported-clause
  cherish2017OriginalReasonsPDF "22" "[73](c), PDF p29"
  conditionalEntitlementChangeReimbursement false false false

sIAClause132and134Reported : CourtReportedClause
sIAClause132and134Reported = court-reported-clause
  cherish2017OriginalReasonsPDF "132 and 134" "[73](e)-(f), PDF p29"
  openSpaceMasterPlanConsistency false false false

sIAClause190and192Reported : CourtReportedClause
sIAClause190and192Reported = court-reported-clause
  cherish2017OriginalReasonsPDF "190 and 192" "[73](g)-(h), PDF pp29-30"
  drainageMasterPlanConsistency false false false

sIAClause215Reported : CourtReportedClause
sIAClause215Reported = court-reported-clause
  cherish2017OriginalReasonsPDF "215" "[73](i), PDF p30"
  councilMayConditionInfrastructurePerformance false false false

sIAClause274Reported : CourtReportedClause
sIAClause274Reported = court-reported-clause
  cherish2017OriginalReasonsPDF "274" "[73](j), PDF p30"
  subdivisionSurveySealingPrerequisites false false false

reportedPriorityClauses : List CourtReportedClause
reportedPriorityClauses =
  sIAClause22Reported ∷
  sIAClause132and134Reported ∷
  sIAClause190and192Reported ∷
  sIAClause215Reported ∷
  sIAClause274Reported ∷ []

-- Even where the court reproduces clause 22's contingent reimbursement
-- mechanism, neither altered entitlement nor actual expenditure/repayment
-- is thereby paid for any 2019/8575 or 2026 parcel.
data EntitlementWorld : Set where
  historicalClauseWithoutCurrentRepayment : EntitlementWorld
  historicalClauseWithNewIndependentRepayment : EntitlementWorld

data ClauseExcerptObservation : Set where
  courtRecordsClause22 : ClauseExcerptObservation

data Actual2026RepaymentReceipt : Set where
  noCurrentFinancialReceipt : Actual2026RepaymentReceipt
  currentFinancialReceiptAuthenticated : Actual2026RepaymentReceipt

clauseExcerpt : EntitlementWorld → ClauseExcerptObservation
clauseExcerpt historicalClauseWithoutCurrentRepayment = courtRecordsClause22
clauseExcerpt historicalClauseWithNewIndependentRepayment = courtRecordsClause22

repaymentStatus : EntitlementWorld → Actual2026RepaymentReceipt
repaymentStatus historicalClauseWithoutCurrentRepayment = noCurrentFinancialReceipt
repaymentStatus historicalClauseWithNewIndependentRepayment = currentFinancialReceiptAuthenticated

repaymentDiffers :
  repaymentStatus historicalClauseWithoutCurrentRepayment ≡
  repaymentStatus historicalClauseWithNewIndependentRepayment → ⊥
repaymentDiffers ()

reportedConditionalReimbursementDoesNotProveCashTransfer :
  INF.FactorsThrough clauseExcerpt repaymentStatus → ⊥
reportedConditionalReimbursementDoesNotProveCashTransfer =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness historicalClauseWithoutCurrentRepayment
      historicalClauseWithNewIndependentRepayment refl repaymentDiffers)

-- Open Space / Drainage masterplans are separately source-paid 1998
-- historical legal planning constructs. They are not an EPBC 2019/8575
-- koala-offset determination, environmental clearance or same-site works.
