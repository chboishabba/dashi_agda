module DASHI.Education.DigitalESDStructuredSearchRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.TypedProvenanceDependencyGraphExact as Provenance
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment
import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact as Paper
import DASHI.Education.DigitalESDStructuredSearchExact as Search
import DASHI.Education.DigitalESDManuscriptDependencyPaymentAdapterExact as Payment

queryFamilyRegression :
  Search.canonicalSearchQueryFamilies
  ≡ Search.digitalEducationESD
  ∷ Search.reflexiveDigitalSustainability
  ∷ Search.lifecycleCircularity
  ∷ Search.participantAgencyGovernance
  ∷ Search.longitudinalInstitutionalImpact
  ∷ Search.openInteroperabilityRepairability
  ∷ []
queryFamilyRegression = refl

openWebExecutionRegression :
  Search.StructuredSearchLedger.openWebSnowballObserved
    Search.canonicalStructuredSearchLedger
  ≡ true
openWebExecutionRegression = refl

scopusExecutionRegression :
  Search.StructuredSearchLedger.scopusExecutionObserved
    Search.canonicalStructuredSearchLedger
  ≡ false
scopusExecutionRegression = refl

wosExecutionRegression :
  Search.StructuredSearchLedger.webOfScienceExecutionObserved
    Search.canonicalStructuredSearchLedger
  ≡ false
wosExecutionRegression = refl

ericExecutionRegression :
  Search.StructuredSearchLedger.ericExecutionObserved
    Search.canonicalStructuredSearchLedger
  ≡ false
ericExecutionRegression = refl

acmExecutionRegression :
  Search.StructuredSearchLedger.acmDigitalLibraryExecutionObserved
    Search.canonicalStructuredSearchLedger
  ≡ false
acmExecutionRegression = refl

ieeeExecutionRegression :
  Search.StructuredSearchLedger.ieeeXploreExecutionObserved
    Search.canonicalStructuredSearchLedger
  ≡ false
ieeeExecutionRegression = refl

structuredSearchStillOpenRegression :
  Paper.closed Paper.transparentStructuredSearch ≡ false
structuredSearchStillOpenRegression = refl

webSnowballDoesNotCloseStructuredSearchRegression :
  Search.OpenWebSnowballClosesTransparentStructuredSearch → ⊥
webSnowballDoesNotCloseStructuredSearchRegression =
  Search.openWebSnowballDoesNotCloseTransparentStructuredSearch

methodSourceDoesNotPromoteSystematicLabelRegression :
  Search.SearchMethodCitationPromotesSystematicReview → ⊥
methodSourceDoesNotPromoteSystematicLabelRegression =
  Search.searchMethodCitationDoesNotPromoteSystematicReview

unexecutedDatabaseDoesNotCreateReceiptRegression :
  Search.PlannedDatabaseCreatesExecutionReceipt → ⊥
unexecutedDatabaseDoesNotCreateReceiptRegression =
  Search.plannedDatabaseDoesNotCreateExecutionReceipt

------------------------------------------------------------------------
-- Executable transparent-search closure.
------------------------------------------------------------------------

closureRequiresExecutedDatabasesRegression :
  (scopusReceipt : Search.DatabaseExecutionReceipt Search.scopus) →
  (wosReceipt : Search.DatabaseExecutionReceipt Search.webOfScience) →
  (ericReceipt : Search.DatabaseExecutionReceipt Search.eric) →
  (acmReceipt : Search.DatabaseExecutionReceipt Search.acmDigitalLibrary) →
  (ieeeReceipt : Search.DatabaseExecutionReceipt Search.ieeeXplore) →
  (dedup : Search.DeduplicationReceipt
    scopusReceipt wosReceipt ericReceipt acmReceipt ieeeReceipt) →
  (screening : Search.EligibilityScreeningReceipt dedup) →
  (extraction : Search.StructuredExtractionReceipt screening) →
  Search.TransparentStructuredSearchClosureReceipt
closureRequiresExecutedDatabasesRegression = Search.closeTransparentStructuredSearch

closureDoesNotPromoteSystematicReviewRegression :
  (receipt : Search.TransparentStructuredSearchClosureReceipt) →
  Search.TransparentStructuredSearchClosureReceipt.promotesSystematicReview receipt
  ≡ false
closureDoesNotPromoteSystematicReviewRegression =
  Search.TransparentStructuredSearchClosureReceipt.promotesSystematicReviewIsFalse

executionReceiptRetainsQueryRegression :
  {surface : Search.SearchSurface} →
  (receipt : Search.DatabaseExecutionReceipt surface) →
  Search.DatabaseExecutionReceipt.queryReferenceRetained receipt ≡ true
executionReceiptRetainsQueryRegression =
  Search.DatabaseExecutionReceipt.queryReferenceRetainedIsTrue

executionReceiptRetainsExportRegression :
  {surface : Search.SearchSurface} →
  (receipt : Search.DatabaseExecutionReceipt surface) →
  Search.DatabaseExecutionReceipt.resultExportRetained receipt ≡ true
executionReceiptRetainsExportRegression =
  Search.DatabaseExecutionReceipt.resultExportRetainedIsTrue

closureWithoutExecutionBlockedRegression :
  Search.UnobservedDatabaseClosesStructuredSearch → ⊥
closureWithoutExecutionBlockedRegression =
  Search.unobservedDatabaseDoesNotCloseStructuredSearch

searchClosureDoesNotCloseSynthesisRegression :
  Search.StructuredSearchClosurePaysEvidenceSynthesis → ⊥
searchClosureDoesNotCloseSynthesisRegression =
  Search.structuredSearchClosureDoesNotPayEvidenceSynthesis

------------------------------------------------------------------------
-- RED: canonical dependency/payment/Pareto cross-pollination.
------------------------------------------------------------------------

canonicalManuscriptDependencyGraphRegression :
  Provenance.TypedDependencyGraph
canonicalManuscriptDependencyGraphRegression =
  Payment.canonicalManuscriptDependencyGraph

searchToEligibleCorpusRequiredRegression :
  Provenance.requiredForTarget Payment.searchToEligibleCorpus ≡ true
searchToEligibleCorpusRequiredRegression = refl

eligibleCorpusToSourceScopeRequiredRegression :
  Provenance.requiredForTarget Payment.eligibleCorpusToSourceScope ≡ true
eligibleCorpusToSourceScopeRequiredRegression = refl

sourceScopeToLifecycleRequiredRegression :
  Provenance.requiredForTarget Payment.sourceScopeToLifecycleSynthesis ≡ true
sourceScopeToLifecycleRequiredRegression = refl

sourceScopeToParticipantGovernanceRequiredRegression :
  Provenance.requiredForTarget Payment.sourceScopeToParticipantGovernanceSynthesis ≡ true
sourceScopeToParticipantGovernanceRequiredRegression = refl

sourceScopeToLongitudinalRequiredRegression :
  Provenance.requiredForTarget Payment.sourceScopeToLongitudinalSynthesis ≡ true
sourceScopeToLongitudinalRequiredRegression = refl

requiredSearchSupportCannotBeResidualizedRegression :
  Payment.RequiredStructuredSearchSupportMayBeResidualized → ⊥
requiredSearchSupportCannotBeResidualizedRegression =
  Payment.requiredStructuredSearchSupportCannotBeResidualized

admittedSearchNarrowingRerunsParetoRegression :
  Feedback.feedbackDisposition
    Assessment.proofPaymentAdmitted
    Assessment.frontierNarrowed
  ≡ Feedback.recomputeFrontier
admittedSearchNarrowingRerunsParetoRegression =
  Payment.admittedSearchNarrowingRerunsPareto

reopenedSearchFrontierRerunsParetoRegression :
  Feedback.feedbackDisposition
    Assessment.proofPaymentContested
    Assessment.frontierReopened
  ≡ Feedback.recomputeFrontier
reopenedSearchFrontierRerunsParetoRegression =
  Payment.reopenedSearchFrontierRerunsPareto

canonicalProvenanceBoundaryRegression :
  Provenance.TypedProvenanceDependencyBoundary.graphCanExposeRequiredDependencies
    Payment.canonicalManuscriptProvenanceBoundary
  ≡ true
canonicalProvenanceBoundaryRegression = refl
