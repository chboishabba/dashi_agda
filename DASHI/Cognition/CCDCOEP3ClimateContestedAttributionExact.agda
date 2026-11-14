module DASHI.Cognition.CCDCOEP3ClimateContestedAttributionExact where

------------------------------------------------------------------------
-- CASE-SPECIFIC SOURCE CONTESTATION, AUTHORISATION AND EXECUTION.
--
-- Historical sources:
-- 1998-04-27 Congressional Record, H2323-H2327: draft API meeting plan.
-- 1998-05-01 Living on Earth interview: attributed API VP response
-- reporting initiative of a lower-level employee; advocacy criticism.
-- 2017-09-05 Washington Post: documented later Cooler Heads advocacy
-- and interviews about its decentralised structure and funding.
-- 2019-10-23 House hearing: subsequent testimony about the 1998 plan.
--
-- Source relevance is not evidence that every plan was implemented,
-- nor that later Coalition acts were on the same execution authority.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DiscriminatorSynthesisExact as D
import DASHI.Cognition.CCDCOEP3API1998PrimaryPlanExact as Plan

data AttributionQuestion : Set where
  planExisted : AttributionQuestion
  groupDraftedPlan : AttributionQuestion
  apiInstitutionApprovedPlan : AttributionQuestion
  specificTacticsImplemented : AttributionQuestion
  campaignCausedOpinionEffect : AttributionQuestion

data SourceDisposition : Set where
  primaryDocument : SourceDisposition
  attributedDenial : SourceDisposition
  investigation : SourceDisposition
  hearingTestimony : SourceDisposition

data HistoricalSource : Set where
  congressionalPlan1998 : HistoricalSource
  attributedAPIResponse1998 : HistoricalSource
  laterCoalitionInvestigation2017 : HistoricalSource
  laterCongressionalHearing2019 : HistoricalSource

sourceDisposition : HistoricalSource → SourceDisposition
sourceDisposition congressionalPlan1998 = primaryDocument
sourceDisposition attributedAPIResponse1998 = attributedDenial
sourceDisposition laterCoalitionInvestigation2017 = investigation
sourceDisposition laterCongressionalHearing2019 = hearingTestimony

-- Evidence categories cannot be substituted as interchangeable data,
-- even if a summary flattens all documents into 'climate campaigning'.
data FlattenedTopic : Set where
  climateDebate : FlattenedTopic

flattenSource : HistoricalSource → FlattenedTopic
flattenSource _ = climateDebate

primaryAndDenialDifferent :
  sourceDisposition congressionalPlan1998
  ≡ sourceDisposition attributedAPIResponse1998 → ⊥
primaryAndDenialDifferent ()

sourceKindNotIdentifiedByTopic :
  NF.FactorsThrough flattenSource sourceDisposition → ⊥
sourceKindNotIdentifiedByTopic =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      congressionalPlan1998
      attributedAPIResponse1998
      refl primaryAndDenialDifferent)

sourceTypeProbe : D.ExperimentBundle HistoricalSource
sourceTypeProbe =
  D.experimentBundle
    SourceDisposition
    sourceDisposition
    1
    "Retain documentary source type, speaker and original claim scope"
    "Source metadata known; not a campaign execution/outcome measurement"

sourceTypeSeparates :
  D.BundleSeparates sourceTypeProbe
    congressionalPlan1998 attributedAPIResponse1998
sourceTypeSeparates =
  D.bundleSeparates primaryAndDenialDifferent

sourceTypeLanguageExtension :
  D.DiscriminatingLanguageExtension flattenSource
sourceTypeLanguageExtension =
  D.discriminatingLanguageExtension
    (D.currentObserverCollision
      congressionalPlan1998 attributedAPIResponse1998 refl)
    sourceTypeProbe sourceTypeSeparates

-- Same confirmed publicly accessible draft can accompany incompatible
-- interpretations of whether API leadership later authorised it.
data InstitutionalAuthorityState : Set where
  approvalAbsent : InstitutionalAuthorityState
  approvalPresent : InstitutionalAuthorityState
  approvalStillUnresolved : InstitutionalAuthorityState

data AuthorityWorld : Set where
  unapprovedWorld : AuthorityWorld
  approvedWorld : AuthorityWorld
  unresolvedWorld : AuthorityWorld

authorityHypothesis : AuthorityWorld → InstitutionalAuthorityState
authorityHypothesis unapprovedWorld = approvalAbsent
authorityHypothesis approvedWorld = approvalPresent
authorityHypothesis unresolvedWorld = approvalStillUnresolved

publishedDraft : AuthorityWorld → Plan.HistoricalActionStage
publishedDraft _ = Plan.draftRecorded

samePublishedDraft :
  publishedDraft unapprovedWorld ≡ publishedDraft approvedWorld
samePublishedDraft = refl

differentAuthorisation :
  authorityHypothesis unapprovedWorld
  ≡ authorityHypothesis approvedWorld → ⊥
differentAuthorisation ()

publishedDraftCannotProveInstitutionalAuthorisation :
  NF.FactorsThrough publishedDraft authorityHypothesis → ⊥
publishedDraftCannotProveInstitutionalAuthorisation =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      unapprovedWorld approvedWorld
      samePublishedDraft differentAuthorisation)

-- Prospective discriminator: an actual source-pinned organisational
-- adoption/vote/approved spending/approval record, not inference
-- from a rhetorical description by either disputant.
authorisationRecordProbe : D.ExperimentBundle AuthorityWorld
authorisationRecordProbe =
  D.experimentBundle
    InstitutionalAuthorityState
    authorityHypothesis
    1
    "Identify original signed authorisation, approval or expenditure records"
    "Synthetic oracle; actual authorisation archive is not yet admitted"

authorisationRecordWouldSeparate :
  D.BundleSeparates authorisationRecordProbe
    unapprovedWorld approvedWorld
authorisationRecordWouldSeparate =
  D.bundleSeparates differentAuthorisation

authorisationLanguageExtension :
  D.DiscriminatingLanguageExtension publishedDraft
authorisationLanguageExtension =
  D.discriminatingLanguageExtension
    (D.currentObserverCollision
      unapprovedWorld approvedWorld samePublishedDraft)
    authorisationRecordProbe authorisationRecordWouldSeparate

-- Separate treatment: verified later public coalition advocacy is not
-- a proof that the same 1998 API action plan was centrally implemented.
data DistinctHistoricalQuestion : Set where
  laterAdvocacyHappened : DistinctHistoricalQuestion
  executed1998Draft : DistinctHistoricalQuestion

data DirectCommandBridge : Set where

noAutomaticLaterAdvocacyTo1998Implementation :
  DirectCommandBridge → ⊥
noAutomaticLaterAdvocacyTo1998Implementation ()

-- The original sources are still separately addressable in case
-- evidence; no source-grade swap, temporal telescoping or auto-promotion.

------------------------------------------------------------------------
-- CONTEMPORANEOUS REPORTED FUNDING AND APPROVAL STATUS.
-- NYT John H. Cushman Jr., 26 April 1998, reprinted in the 27 April
-- 1998 Congressional Record ahead of the draft. Joe Walker reportedly
-- told the journalist no industry executives had been approached to
-- fund the still-tentative plan. Industry representatives reportedly
-- said participating organisations had not formally approved it.
--
-- This is a dated ATTRIBUTED REPORT as of April 25–26, not proof of
-- permanent absence of funding or subsequent campaign implementation.
------------------------------------------------------------------------

record Original1998FundingStatusReport : Set where
  constructor original1998FundingStatusReport
  field
    sourceLocator : String
    reportDate : String
    organiserHadNotApproachedExecutiveFunders : Bool
    organisationsReportedNoFormalApproval : Bool
    actualFinalApprovalReceiptPresent : Bool
    actualFinalFundingReceiptPresent : Bool

contemporaneousNoApprovalReport : Original1998FundingStatusReport
contemporaneousNoApprovalReport =
  original1998FundingStatusReport
    "NYT John H. Cushman Jr. 1998-04-26, reprinted Congressional Record H2325"
    "1998-04-26"
    true
    true
    false
    false

actualApprovalNotEstablished :
  Original1998FundingStatusReport.actualFinalApprovalReceiptPresent
    contemporaneousNoApprovalReport ≡ false
actualApprovalNotEstablished = refl

actualFundingNotEstablished :
  Original1998FundingStatusReport.actualFinalFundingReceiptPresent
    contemporaneousNoApprovalReport ≡ false
actualFundingNotEstablished = refl

-- The later Walker "never funded" statement is reproduced by
-- SourceWatch. Without authentic original correspondence and independent
-- accounting, it is attributed testimony only, not a certified negative.
record RetrospectiveAttribution : Set where
  constructor retrospectiveAttribution
  field
    secondarySource : String
    speaker : String
    originalInterviewAuthenticated : Bool
    negativeAccountingIndependentReceipt : Bool

walkerAttributedRetrospective : RetrospectiveAttribution
walkerAttributedRetrospective =
  retrospectiveAttribution
    "SourceWatch Joseph L. Walker III, retrospective statement"
    "Joseph L. Walker III"
    false
    false

retrospectiveIsNotFundProof :
  RetrospectiveAttribution.negativeAccountingIndependentReceipt
    walkerAttributedRetrospective ≡ false
retrospectiveIsNotFundProof = refl

------------------------------------------------------------------------
-- DIRECT RETROSPECTIVE NAMED EXECUTIVE INTERVIEW, April 20, 2021:
-- Russell Cook interviews William O'Keefe (former API VP/COO).
-- Original publisher: https://gelbspanfiles.com/?p=11851
--
-- This source is a directly published first-person RESPONSE (stronger
-- provenance than a secondary paraphrase). The interviewer is an
-- advocate disputing public climate-influence allegations, and the
-- participant's account is potentially interested. No independent
-- financial records or original interview audio are admitted.
--
-- O'Keefe says the proposed API plan was never funded/implemented;
-- API hosted a MULTI-ORGANISATION workshop, not just Walker acting alone;
-- and disputes the wording of the 1998 Living on Earth account.
-- Never collapse a planning workshop into plan implementation, or a
-- nonimplementation claim into absence of parallel industry advocacy.
------------------------------------------------------------------------

record FormerExecutive2021Account : Set where
  constructor formerExecutive2021Account
  field
    publishedTranscriptLocator : String
    participantName : String
    publishedInterviewDate : String
    saysSpecificPlanNeverFunded : Bool
    saysSpecificPlanNeverImplemented : Bool
    saysMultiOrganisationWorkshopOccurred : Bool
    disputesEarlierAttribution : Bool
    originalAudioAuthenticated : Bool
    independentCompanyAccountingAdmitted : Bool

okeefe2021AttributedAccount : FormerExecutive2021Account
okeefe2021AttributedAccount =
  formerExecutive2021Account
    "Russell Cook, William O'Keefe interview, GelbspanFiles, 2021-04-20"
    "William O'Keefe"
    "2021-04-20"
    true true true true false false

publishedNamedParticipantSaysNoFunding :
  FormerExecutive2021Account.saysSpecificPlanNeverFunded
    okeefe2021AttributedAccount ≡ true
publishedNamedParticipantSaysNoFunding = refl

publishedNamedParticipantSaysPlanningOccurred :
  FormerExecutive2021Account.saysMultiOrganisationWorkshopOccurred
    okeefe2021AttributedAccount ≡ true
publishedNamedParticipantSaysPlanningOccurred = refl

directInterviewIsNotIndependentAccounting :
  FormerExecutive2021Account.independentCompanyAccountingAdmitted
    okeefe2021AttributedAccount ≡ false
directInterviewIsNotIndependentAccounting = refl

originalInterviewAudioStillNotAuthenticated :
  FormerExecutive2021Account.originalAudioAuthenticated
    okeefe2021AttributedAccount ≡ false
originalInterviewAudioStillNotAuthenticated = refl
