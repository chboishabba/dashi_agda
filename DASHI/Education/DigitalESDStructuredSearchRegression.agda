module DASHI.Education.DigitalESDStructuredSearchRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact as Paper
import DASHI.Education.DigitalESDStructuredSearchExact as Search

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
-- RED surface for executable transparent-search closure.
------------------------------------------------------------------------

closureRequiresExecutedDatabasesRegression :
  Search.DatabaseExecutionReceipt Search.scopus →
  Search.DatabaseExecutionReceipt Search.webOfScience →
  Search.DatabaseExecutionReceipt Search.eric →
  Search.DatabaseExecutionReceipt Search.acmDigitalLibrary →
  Search.DatabaseExecutionReceipt Search.ieeeXplore →
  Search.DeduplicationReceipt →
  Search.EligibilityScreeningReceipt →
  Search.StructuredExtractionReceipt →
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
