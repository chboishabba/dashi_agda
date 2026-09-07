module DASHI.Law.SensibLawProofSearchResultAssessmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawCitationUsePropositionExact as CitationUse

------------------------------------------------------------------------
-- SEARCH RESULT ASSESSMENT
--
-- A backend result becomes useful only after proposition attribution,
-- authority/treatment classification, consumer applicability and proof-payment
-- review. Retrieval itself never closes the gap.
------------------------------------------------------------------------

data ResultAttributionStatus : Set where
  resultAttributionUnresolved : ResultAttributionStatus
  resultAttributedToCourt : ResultAttributionStatus
  resultAttributedToJudge : ResultAttributionStatus
  resultAttributedToParty : ResultAttributionStatus
  resultAttributedToExternalSource : ResultAttributionStatus


data ConsumerApplicabilityAssessment : Set where
  consumerApplicabilityUnresolved : ConsumerApplicabilityAssessment
  consumerApplicabilityCandidate : ConsumerApplicabilityAssessment
  consumerApplicabilityAdmitted : ConsumerApplicabilityAssessment
  consumerInapplicabilityAdmitted : ConsumerApplicabilityAssessment


data ProofPaymentAssessment : Set where
  proofPaymentUnresolved : ProofPaymentAssessment
  proofPaymentCandidate : ProofPaymentAssessment
  proofPaymentAdmitted : ProofPaymentAssessment
  proofPaymentRejected : ProofPaymentAssessment
  proofPaymentContested : ProofPaymentAssessment


record RetrievedPassage : Set₁ where
  constructor retrievedPassage
  field
    compiledQuery : Query.ProviderCompiledQuery
    documentReference : String
    passageReference : String
    textReference : String
    retrievalRankReference : String
    retrievalReference : String

open RetrievedPassage public

record AttributedSearchProposition (passage : RetrievedPassage) : Set₁ where
  constructor attributedSearchProposition
  field
    propositionReference : String
    attribution : ResultAttributionStatus
    citationUse : CitationUse.CitationUseStatus
    treatment : CitationUse.AuthorityTreatmentStatus
    currentAuthority : CitationUse.CurrentAuthorityStatus
    attributionReceipt : Set
    propositionReferenceReceipt : Set
    assessmentReference : String

open AttributedSearchProposition public

record SearchResultProofAssessment
    {passage : RetrievedPassage}
    (proposition : AttributedSearchProposition passage) : Set₁ where
  constructor searchResultProofAssessment
  field
    consumerReference : String
    applicability : ConsumerApplicabilityAssessment
    proofPayment : ProofPaymentAssessment
    authorityFitnessReceipt : Set
    treatmentFitnessReceipt : Set
    temporalFitnessReceipt : Set
    jurisdictionFitnessReceipt : Set
    propositionCorrespondenceReceipt : Set
    assessmentReference : String

open SearchResultProofAssessment public

------------------------------------------------------------------------
-- Frontier delta.
------------------------------------------------------------------------

data FrontierChange : Set where
  frontierUnchanged : FrontierChange
  frontierNarrowed : FrontierChange
  frontierReopened : FrontierChange
  frontierClosed : FrontierChange
  frontierContradicted : FrontierChange
  frontierUnderidentified : FrontierChange


data NonProgressReason : Set where
  duplicateResult : NonProgressReason
  dominatedResult : NonProgressReason
  sameProofContribution : NonProgressReason
  authorityInferiorResult : NonProgressReason
  wrongConsumerResult : NonProgressReason
  wrongPropositionShapeResult : NonProgressReason


record SearchFrontierDelta : Set₁ where
  constructor searchFrontierDelta
  field
    consumerReference : String
    priorFrontierReference : String
    posteriorFrontierReference : String
    change : FrontierChange
    firstResidualBeforeReference : String
    firstResidualAfterReference : String
    proofContributionReference : String
    deltaReference : String

open SearchFrontierDelta public

record NonProgressingSearchResult : Set where
  constructor nonProgressingSearchResult
  field
    resultReference : String
    reason : NonProgressReason
    consumerReference : String
    reasonReceipt : Set
    nonProgressReference : String

open NonProgressingSearchResult public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SearchRankMeansAuthorityFitness : Set where
data PassageMeansAttributedProposition : Set where
data AttributedPropositionMeansApplicable : Set where
data ApplicableCandidateMeansProofPaid : Set where
data FrontierUnchangedMeansNoKnowledgeGain : Set where

rankDoesNotMeanAuthority : SearchRankMeansAuthorityFitness → ⊥
rankDoesNotMeanAuthority ()

passageDoesNotDetermineAttribution : PassageMeansAttributedProposition → ⊥
passageDoesNotDetermineAttribution ()

attributionDoesNotMeanApplicability : AttributedPropositionMeansApplicable → ⊥
attributionDoesNotMeanApplicability ()

candidateApplicabilityDoesNotPayProof : ApplicableCandidateMeansProofPaid → ⊥
candidateApplicabilityDoesNotPayProof ()

unchangedFrontierDoesNotMeanNoKnowledgeGain : FrontierUnchangedMeansNoKnowledgeGain → ⊥
unchangedFrontierDoesNotMeanNoKnowledgeGain ()

record ResultAssessmentBoundary : Set where
  constructor resultAssessmentBoundary
  field
    retrievalAndAssessmentSeparated : Bool
    retrievalAndAssessmentSeparatedIsTrue : retrievalAndAssessmentSeparated ≡ true
    attributionAndAuthoritySeparated : Bool
    attributionAndAuthoritySeparatedIsTrue : attributionAndAuthoritySeparated ≡ true
    applicabilityAndProofPaymentSeparated : Bool
    applicabilityAndProofPaymentSeparatedIsTrue :
      applicabilityAndProofPaymentSeparated ≡ true
    resultRankEqualsProofPayment : Bool
    resultRankEqualsProofPaymentIsFalse : resultRankEqualsProofPayment ≡ false
    frontierDeltaIsConsumerIndexed : Bool
    frontierDeltaIsConsumerIndexedIsTrue : frontierDeltaIsConsumerIndexed ≡ true

canonicalResultAssessmentBoundary : ResultAssessmentBoundary
canonicalResultAssessmentBoundary =
  resultAssessmentBoundary true refl true refl true refl false refl true refl
