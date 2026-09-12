module DASHI.Governance.AustralianSenateAutismInquiryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- AUSTRALIAN SENATE SELECT COMMITTEE ON AUTISM
--
-- Source-bound parliamentary formalisation. This owner distinguishes inquiry
-- procedure, submitted evidence, committee findings/recommendations,
-- government responses and later policy implementation. No transition in
-- that chain is automatic.
------------------------------------------------------------------------

senateInquiryHome : Source.AttributedSource
senateInquiryHome = Source.mkNoDOISource
  "Parliament of Australia — Senate Select Committee on Autism"
  "Autism inquiry"
  "Parliament of Australia"
  "2019–2022"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Autism"
  Source.governmentSource
  "Primary parliamentary carrier for inquiry identity, status, hearings, submissions, report and government-response navigation."
  Source.publicAttribution

senateAutismReport : Source.AttributedSource
senateAutismReport = Source.mkNoDOISource
  "Senate Select Committee on Autism"
  "Services, support and life outcomes for autistic Australians"
  "Parliament of Australia"
  "2022"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Autism/autism/Report"
  Source.governmentSource
  "Primary committee report carrier for committee views and recommendations; committee statements are not silently promoted to enacted law, empirical truth or implemented policy."
  Source.publicAttribution

senateAutismRecommendations : Source.AttributedSource
senateAutismRecommendations = Source.mkNoDOISource
  "Senate Select Committee on Autism"
  "Recommendations — Services, support and life outcomes for autistic Australians"
  "Parliament of Australia"
  "2022"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Autism/autism/Report/Section?id=committees%2Freportsen%2F024412%2F72466"
  Source.governmentSource
  "Primary proposition-level carrier for numbered committee recommendations."
  Source.publicAttribution

senateAutismGovernmentResponse : Source.AttributedSource
senateAutismGovernmentResponse = Source.mkNoDOISource
  "Australian Government"
  "Australian Government response to the Senate Select Committee on Autism"
  "Parliament of Australia"
  "2022"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Autism/autism/Government_Response"
  Source.governmentSource
  "Primary response carrier for government positions on committee recommendations; support or support-in-principle does not itself prove implementation or outcomes."
  Source.publicAttribution

nationalAutismStrategy2025 : Source.AttributedSource
nationalAutismStrategy2025 = Source.mkNoDOISource
  "Australian Government Department of Social Services"
  "National Autism Strategy 2025–2031"
  "Department of Social Services"
  "2025"
  "https://www.dss.gov.au/national-autism-strategy/resource/national-autism-strategy-2025-2031"
  Source.governmentSource
  "Downstream policy carrier. It may discharge selected implementation coordinates only through an explicit same-recommendation/application weld."
  Source.publicAttribution

autismInquirySources : List Source.AttributedSource
autismInquirySources =
  senateInquiryHome ∷
  senateAutismReport ∷
  senateAutismRecommendations ∷
  senateAutismGovernmentResponse ∷
  nationalAutismStrategy2025 ∷
  []

autismInquiryAtlas : Source.AttributedSourceAtlas
autismInquiryAtlas = Source.mkSourceAtlas
  "Australian Senate autism inquiry source atlas"
  "DASHI.Governance.AustralianSenateAutismInquiryExact"
  autismInquirySources
  "Primary parliamentary inquiry/report/recommendation/response objects plus the downstream National Autism Strategy, with non-promotion boundaries preserved."

------------------------------------------------------------------------
-- Identifier / bibliographic discipline.
------------------------------------------------------------------------

senateAutismReportISBN : String
senateAutismReportISBN = "978-1-76093-383-8"

senateAutismReportDOIState : Source.DOIState
senateAutismReportDOIState = Source.noDOIRecordedByAtlas

wikidataQIDState : String
wikidataQIDState = "exact same-object QID unresolved by current atlas; do not invent or import an adjacent autism/parliament entity QID"

deweyCoordinateState : String
deweyCoordinateState = "exact report-level Dewey coordinate unresolved by current atlas; Dewey is navigation metadata only"

oeisCoordinateState : String
oeisCoordinateState = "not applicable to this parliamentary source tranche"

oeisSuppliesNoAuthority : Bool
oeisSuppliesNoAuthority = false

------------------------------------------------------------------------
-- Parliamentary manifestation and temporal-event separation.
------------------------------------------------------------------------

data ParliamentaryManifestation : Set where
  termsOfReference : ParliamentaryManifestation
  submittedEvidence : ParliamentaryManifestation
  committeeFinding : ParliamentaryManifestation
  committeeRecommendation : ParliamentaryManifestation
  dissentingReport : ParliamentaryManifestation
  governmentResponse : ParliamentaryManifestation
  policyStrategy : ParliamentaryManifestation
  implementedAction : ParliamentaryManifestation
  measuredOutcome : ParliamentaryManifestation

data InquiryEvent : Set where
  referred2019-11-27 : InquiryEvent
  reportPresentedOOS2022-03-25 : InquiryEvent
  reportTabled2022-03-28 : InquiryEvent
  governmentResponsePresented2022-12-08 : InquiryEvent
  strategyReleased2025-01-14 : InquiryEvent

------------------------------------------------------------------------
-- Paid proposition fibres. These are bounded source propositions, not free
-- claims about the world.
------------------------------------------------------------------------

data AutismInquiryProposition : Set where
  inquiryEstablishedForAutismServicesOutcomesAndStrategy : AutismInquiryProposition
  reportContainsEightyOneRecommendations : AutismInquiryProposition
  recommendation1NationalAutismStrategy : AutismInquiryProposition
  recommendation2CoDesign : AutismInquiryProposition
  recommendation18IntersectionalFocus : AutismInquiryProposition
  recommendation26ResearchFramework : AutismInquiryProposition
  recommendation27DataCollection : AutismInquiryProposition
  recommendation30AutismSpecificAdvocacy : AutismInquiryProposition
  governmentResponseSupportsRecommendation1 : AutismInquiryProposition
  strategyExists2025To2031 : AutismInquiryProposition
  greensDissentExists : AutismInquiryProposition

data PropositionPaymentStatus : Set where
  externalRecordPaid : PropositionPaymentStatus
  downstreamSameObjectWeldOpen : PropositionPaymentStatus
  implementationPaymentOpen : PropositionPaymentStatus
  outcomePaymentOpen : PropositionPaymentStatus

record AttributedAutismInquiryFact : Set where
  constructor attributed-autism-inquiry-fact
  field
    proposition : AutismInquiryProposition
    manifestation : ParliamentaryManifestation
    source : Source.AttributedSource
    exactLocator : String
    boundedStatement : String
    status : PropositionPaymentStatus
    sourceIdentityImportsTruth : Bool
    sourceIdentityImportsTruthIsFalse : sourceIdentityImportsTruth ≡ false

open AttributedAutismInquiryFact public

recommendation1Fact : AttributedAutismInquiryFact
recommendation1Fact = attributed-autism-inquiry-fact
  recommendation1NationalAutismStrategy
  committeeRecommendation
  senateAutismRecommendations
  "Recommendation 1 / paragraph 5.62"
  "The committee recommended development of a National Autism Strategy and accompanying implementation, nationally coordinated and whole-of-life in orientation."
  externalRecordPaid false refl

recommendation2Fact : AttributedAutismInquiryFact
recommendation2Fact = attributed-autism-inquiry-fact
  recommendation2CoDesign
  committeeRecommendation
  senateAutismRecommendations
  "Recommendation 2 / paragraph 5.67"
  "The committee recommended a co-design approach drawing on the autistic community together with parents, carers, researchers and policy makers."
  externalRecordPaid false refl

recommendation18Fact : AttributedAutismInquiryFact
recommendation18Fact = attributed-autism-inquiry-fact
  recommendation18IntersectionalFocus
  committeeRecommendation
  senateAutismReport
  "Chapter 7 / Recommendation 18 / paragraph 7.79"
  "The committee recommended particular focus on autistic adults, women and girls, lower-socioeconomic groups, regional and remote people, First Nations people, culturally and linguistically diverse people, gender-diverse and non-heterosexual people, and people with complex needs."
  externalRecordPaid false refl

recommendation26Fact : AttributedAutismInquiryFact
recommendation26Fact = attributed-autism-inquiry-fact
  recommendation26ResearchFramework
  committeeRecommendation
  senateAutismRecommendations
  "Recommendation 26 / paragraph 8.43"
  "The committee recommended a National Autism Research Framework under the National Autism Strategy."
  externalRecordPaid false refl

recommendation27Fact : AttributedAutismInquiryFact
recommendation27Fact = attributed-autism-inquiry-fact
  recommendation27DataCollection
  committeeRecommendation
  senateAutismRecommendations
  "Recommendation 27 / paragraph 8.44"
  "The committee recommended investigating improved data collection about autistic people to inform research, policy and practice."
  externalRecordPaid false refl

recommendation30Fact : AttributedAutismInquiryFact
recommendation30Fact = attributed-autism-inquiry-fact
  recommendation30AutismSpecificAdvocacy
  committeeRecommendation
  senateAutismRecommendations
  "Recommendation 30 / paragraph 9.57"
  "The committee recommended a National Autism Advocacy Plan including actions to encourage autism-specific advocacy services, including autistic-led services."
  externalRecordPaid false refl

responseRecommendation1Fact : AttributedAutismInquiryFact
responseRecommendation1Fact = attributed-autism-inquiry-fact
  governmentResponseSupportsRecommendation1
  governmentResponse
  senateAutismGovernmentResponse
  "Government response / Recommendation 1"
  "The Australian Government recorded Recommendation 1 as supported, while noting full development and implementation could take longer than 12 months."
  externalRecordPaid false refl

strategyExistenceFact : AttributedAutismInquiryFact
strategyExistenceFact = attributed-autism-inquiry-fact
  strategyExists2025To2031
  policyStrategy
  nationalAutismStrategy2025
  "National Autism Strategy 2025–2031 / publication metadata"
  "The Department of Social Services published the National Autism Strategy 2025–2031 on 14 January 2025."
  externalRecordPaid false refl

------------------------------------------------------------------------
-- Ordered snowball. Acquisition may occur out of dependency order; payment
-- may not skip identity/proposition/same-object/application dependencies.
------------------------------------------------------------------------

data SnowballLeaf : Set where
  inquiryIdentityLeaf : SnowballLeaf
  numberedRecommendationLeaf : SnowballLeaf
  governmentResponseLeaf : SnowballLeaf
  strategySameObjectLeaf : SnowballLeaf
  implementationEvidenceLeaf : SnowballLeaf
  outcomeEvidenceLeaf : SnowballLeaf

orderedPaymentFrontier : SnowballLeaf
orderedPaymentFrontier = strategySameObjectLeaf

acquisitionMayRunAheadOfPayment : Bool
acquisitionMayRunAheadOfPayment = true

strategyExistencePaysImplementation : Bool
strategyExistencePaysImplementation = false

strategyExistencePaysOutcome : Bool
strategyExistencePaysOutcome = false

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data SubmissionStatementEqualsEstablishedFact : Set where
data CommitteeFindingEqualsBindingLaw : Set where
data CommitteeRecommendationEqualsImplementation : Set where
data GovernmentSupportEqualsImplementation : Set where
data StrategyTextEqualsMeasuredOutcome : Set where
data DissentEqualsMajorityFinding : Set where

submissionStatementDoesNotEqualEstablishedFact :
  SubmissionStatementEqualsEstablishedFact → ⊥
submissionStatementDoesNotEqualEstablishedFact ()

committeeFindingDoesNotEqualBindingLaw :
  CommitteeFindingEqualsBindingLaw → ⊥
committeeFindingDoesNotEqualBindingLaw ()

committeeRecommendationDoesNotEqualImplementation :
  CommitteeRecommendationEqualsImplementation → ⊥
committeeRecommendationDoesNotEqualImplementation ()

governmentSupportDoesNotEqualImplementation :
  GovernmentSupportEqualsImplementation → ⊥
governmentSupportDoesNotEqualImplementation ()

strategyTextDoesNotEqualMeasuredOutcome :
  StrategyTextEqualsMeasuredOutcome → ⊥
strategyTextDoesNotEqualMeasuredOutcome ()

dissentDoesNotEqualMajorityFinding :
  DissentEqualsMajorityFinding → ⊥
dissentDoesNotEqualMajorityFinding ()

------------------------------------------------------------------------
-- Intersectional non-factorability.
------------------------------------------------------------------------

data SituatedAutisticState : Set where
  sameAutismLabelRemoteFirstNationsComplexNeeds : SituatedAutisticState
  sameAutismLabelMetroLowSupportNeed : SituatedAutisticState

data AutismOnlySurface : Set where
  autisticPersonSurface : AutismOnlySurface

data SituatedSupportNeed : Set where
  highCoordinationCulturallySituatedNeed : SituatedSupportNeed
  lowerCoordinationGenericAccessNeed : SituatedSupportNeed

autismOnlyObserver : SituatedAutisticState → AutismOnlySurface
autismOnlyObserver _ = autisticPersonSurface

situatedSupportNeed : SituatedAutisticState → SituatedSupportNeed
situatedSupportNeed sameAutismLabelRemoteFirstNationsComplexNeeds =
  highCoordinationCulturallySituatedNeed
situatedSupportNeed sameAutismLabelMetroLowSupportNeed =
  lowerCoordinationGenericAccessNeed

situatedSupportNeedDiffers :
  situatedSupportNeed sameAutismLabelRemoteFirstNationsComplexNeeds ≡
  situatedSupportNeed sameAutismLabelMetroLowSupportNeed → ⊥
situatedSupportNeedDiffers ()

autismLabelCannotRecoverSituatedNeed :
  INF.FactorsThrough autismOnlyObserver situatedSupportNeed → ⊥
autismLabelCannotRecoverSituatedNeed =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameAutismLabelRemoteFirstNationsComplexNeeds
      sameAutismLabelMetroLowSupportNeed
      refl
      situatedSupportNeedDiffers)

------------------------------------------------------------------------
-- Pareto frontier for the next acquisition round.
------------------------------------------------------------------------

data AcquisitionPriority : Set where
  exactStrategyToRecommendationWeld : AcquisitionPriority
  recommendationByRecommendationResponseStatus : AcquisitionPriority
  implementationActionEvidence : AcquisitionPriority
  outcomeMeasurementEvidence : AcquisitionPriority

highestAlphaInvestigativePareto : AcquisitionPriority
highestAlphaInvestigativePareto = exactStrategyToRecommendationWeld

record AutismInquiryBoundary : Set where
  constructor autism-inquiry-boundary
  field
    submissionSeparatedFromTruth : Bool
    recommendationSeparatedFromImplementation : Bool
    responseSeparatedFromImplementation : Bool
    strategySeparatedFromOutcome : Bool
    dissentSeparatedFromMajority : Bool
    intersectionalAxesNotCollapsed : Bool
    qidNotInvented : Bool
    deweyNotPromoted : Bool
    oeisNotApplicableAndNonAuthoritative : Bool

canonicalAutismInquiryBoundary : AutismInquiryBoundary
canonicalAutismInquiryBoundary =
  autism-inquiry-boundary true true true true true true true true true
