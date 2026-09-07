module DASHI.Law.SensibLawCitationAuthorityFollowExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProductionLegalRuntimeABIExact as Runtime
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent

------------------------------------------------------------------------
-- CITATION-DIRECTED AUTHORITY FOLLOW
--
-- Exact citation occurrence, source identity, acquisition, parser re-entry and
-- proposition use are separate promotion stages.
------------------------------------------------------------------------

record CitationCandidate : Set where
  constructor citationCandidate
  field
    citingDocumentReference : String
    citingSpanReference : String
    rawCitationText : String
    candidateReference : String

open CitationCandidate public

record CitationIdentity (candidate : CitationCandidate) : Set where
  constructor citationIdentity
  field
    normalizedCitation : String
    authorityStableReference : String
    identityResolutionReceipt : Set
    identityReference : String

open CitationIdentity public

data CitationAcquisitionState : Set where
  authorityAlreadyInCorpus : CitationAcquisitionState
  authorityFetched : CitationAcquisitionState
  authorityFetchUnresolved : CitationAcquisitionState
  authorityFetchBlocked : CitationAcquisitionState


record ExactAuthorityAcquisition
    {candidate : CitationCandidate}
    (identity : CitationIdentity candidate) : Set₁ where
  constructor exactAuthorityAcquisition
  field
    state : CitationAcquisitionState
    providerReference : String
    acquiredDocumentReference : String
    parentCitationReference : String
    boundedAcquisitionReceipt : Set
    acquisitionReference : String

open ExactAuthorityAcquisition public

record CitationPNFReentry
    {candidate : CitationCandidate}
    {identity : CitationIdentity candidate}
    (acquisition : ExactAuthorityAcquisition identity) : Set₁ where
  constructor citationPNFReentry
  field
    pnf : Runtime.RuntimePNFReceipt
    sameAcquiredDocumentReceipt : Set
    citationIdentityPreservedReceipt : Set
    reentryReference : String

open CitationPNFReentry public

------------------------------------------------------------------------
-- Citation-follow search intent. Exact citation lookup is a producer, not a
-- conclusion about what the authority was used to prove.
------------------------------------------------------------------------

exactCitationProducer : Intent.ProducerClass
exactCitationProducer = Intent.exactCitedAuthorityProducer

record CitationFollowPlan : Set₁ where
  constructor citationFollowPlan
  field
    candidate : CitationCandidate
    identity : CitationIdentity candidate
    producer : Intent.ProducerClass
    producerIsExactCitation : producer ≡ Intent.exactCitedAuthorityProducer
    jurisdictionReference : String
    preferredProviderReference : String
    maxDepthReference : String
    planReference : String

open CitationFollowPlan public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CitationOccurrenceAutomaticallyAdoption : Set where
data CitationIdentityAutomaticallyAuthorityForProposition : Set where
data AcquiredAuthorityAutomaticallyPropositionPayment : Set where
data CitedCaseAutomaticallyBindingNow : Set where
data CitedCaseAutomaticallyRatio : Set where
data ParserMayInferCitationTreatmentFromCitationExistence : Set where

citationDoesNotMeanAdoption : CitationOccurrenceAutomaticallyAdoption → ⊥
citationDoesNotMeanAdoption ()

identityDoesNotMeanAuthorityForTarget :
  CitationIdentityAutomaticallyAuthorityForProposition → ⊥
identityDoesNotMeanAuthorityForTarget ()

acquisitionDoesNotPayProposition :
  AcquiredAuthorityAutomaticallyPropositionPayment → ⊥
acquisitionDoesNotPayProposition ()

citedCaseDoesNotBecomeCurrentBindingAuthority : CitedCaseAutomaticallyBindingNow → ⊥
citedCaseDoesNotBecomeCurrentBindingAuthority ()

citedCaseDoesNotBecomeRatio : CitedCaseAutomaticallyRatio → ⊥
citedCaseDoesNotBecomeRatio ()

parserDoesNotInferTreatmentFromExistence :
  ParserMayInferCitationTreatmentFromCitationExistence → ⊥
parserDoesNotInferTreatmentFromExistence ()

record CitationFollowBoundary : Set where
  constructor citationFollowBoundary
  field
    citationOccurrenceAndIdentitySeparated : Bool
    citationOccurrenceAndIdentitySeparatedIsTrue :
      citationOccurrenceAndIdentitySeparated ≡ true
    identityAndAcquisitionSeparated : Bool
    identityAndAcquisitionSeparatedIsTrue : identityAndAcquisitionSeparated ≡ true
    acquisitionReentersSamePNF : Bool
    acquisitionReentersSamePNFIsTrue : acquisitionReentersSamePNF ≡ true
    citationMeansAdoption : Bool
    citationMeansAdoptionIsFalse : citationMeansAdoption ≡ false
    acquisitionMeansProofPayment : Bool
    acquisitionMeansProofPaymentIsFalse : acquisitionMeansProofPayment ≡ false

canonicalCitationFollowBoundary : CitationFollowBoundary
canonicalCitationFollowBoundary =
  citationFollowBoundary true refl true refl true refl false refl false refl
