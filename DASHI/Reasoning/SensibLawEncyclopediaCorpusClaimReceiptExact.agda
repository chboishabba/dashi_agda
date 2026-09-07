module DASHI.Reasoning.SensibLawEncyclopediaCorpusClaimReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.SourceProvenanceExact as Source
import DASHI.Reasoning.SensibLawCorpusWorldPNFBridgeExact as CorpusWorld

------------------------------------------------------------------------
-- EDITION-INDEXED ENCYCLOPEDIA CLAIM RECEIPTS
--
-- This owner is deliberately corpus-generic: Encarta, Britannica, World Book,
-- Columbia, Wikipedia snapshots, or another bounded reference corpus may use
-- the same carrier.  It records what a particular edition/article/passage
-- asserts.  It does not promote that assertion to world truth or to authority
-- sufficient for an arbitrary downstream consumer.
------------------------------------------------------------------------

data EncyclopediaProductionModel : Set where
  curatedEdition : EncyclopediaProductionModel
  continuouslyRevised : EncyclopediaProductionModel
  otherReferenceProduction : EncyclopediaProductionModel

record EncyclopediaCorpusIdentity : Set where
  constructor encyclopediaCorpusIdentity
  field
    corpusReference : String
    corpusTitle : String
    publisherReference : String
    productionModel : EncyclopediaProductionModel
open EncyclopediaCorpusIdentity public

record EncyclopediaEditionIdentity : Set where
  constructor encyclopediaEditionIdentity
  field
    corpus : EncyclopediaCorpusIdentity
    editionIdentifier : String
    publicationDateReference : String
    releaseLabel : String
    mediumReference : String
    localeReference : String
    editionContentHash : String
    editionManifestReference : String
open EncyclopediaEditionIdentity public

record EncyclopediaEntryIdentity : Set where
  constructor encyclopediaEntryIdentity
  field
    stableEntryIdentifier : String
    canonicalTitle : String
    subjectIdentityReference : String
open EncyclopediaEntryIdentity public

record EncyclopediaEntryVersion : Set where
  constructor encyclopediaEntryVersion
  field
    edition : EncyclopediaEditionIdentity
    entry : EncyclopediaEntryIdentity
    entryVersionReference : String
    entryContentHash : String
open EncyclopediaEntryVersion public

record ExactPassageCarrier : Set where
  constructor exactPassageCarrier
  field
    entryVersion : EncyclopediaEntryVersion
    passageReference : String
    exactSpanReference : String
    exactTextHash : String
open ExactPassageCarrier public

record EncyclopedicTemporalScope : Set where
  constructor encyclopedicTemporalScope
  field
    publicationTimeReference : String
    subjectTimeReference : String
open EncyclopedicTemporalScope public

record EncyclopediaExtractionReceipt : Set where
  constructor encyclopediaExtractionReceipt
  field
    carrier : ExactPassageCarrier
    propositionReference : String
    extractionMethodReference : String
    extractionReceiptReference : String
open EncyclopediaExtractionReceipt public

data EditorialReviewStatus : Set where
  reviewUnspecified : EditorialReviewStatus
  editoriallyReviewed : EditorialReviewStatus
  namedAuthorReviewed : EditorialReviewStatus
  communityReviewed : EditorialReviewStatus

record EncyclopediaAuthorityAssessment : Set where
  constructor encyclopediaAuthorityAssessment
  field
    reviewStatus : EditorialReviewStatus
    authorReference : String
    editorialAuthorityReference : String
    domainReference : String
    citationsReference : String
    assessmentReference : String
open EncyclopediaAuthorityAssessment public

record CorpusClaimReceipt : Set where
  constructor corpusClaimReceipt
  field
    extraction : EncyclopediaExtractionReceipt
    temporalScope : EncyclopedicTemporalScope
    authorityAssessment : EncyclopediaAuthorityAssessment
    sourceAssertionReference : String
    sourceBoundaryReference : String
open CorpusClaimReceipt public

------------------------------------------------------------------------
-- Existing SensibLaw/DASHI adapters.
------------------------------------------------------------------------

claimSourceReceipt : CorpusClaimReceipt → Source.SourceReceipt
claimSourceReceipt r =
  Source.sourceReceipt
    Source.externalReferencedSourceLayer
    (corpusReference
      (corpus
        (edition
          (entryVersion
            (carrier (extraction r))))))
    (stableEntryIdentifier
      (entry
        (entryVersion
          (carrier (extraction r)))))
    (entryVersionReference
      (entryVersion
        (carrier (extraction r))))
    (exactTextHash (carrier (extraction r)))
    (sourceBoundaryReference r)

claimToCitedSourceHorizon :
  (r : CorpusClaimReceipt) →
  CorpusWorld.ResolutionStatus →
  String →
  CorpusWorld.EvidentialPNFHorizonProvenance
claimToCitedSourceHorizon r status unresolved =
  CorpusWorld.evidentialPNFHorizonProvenance
    (propositionReference (extraction r))
    CorpusWorld.citedSourceCorpusHorizon
    status
    (sourceAssertionReference r)
    unresolved

claimHorizonIsCitedSourceCorpus :
  (r : CorpusClaimReceipt) →
  (status : CorpusWorld.ResolutionStatus) →
  (unresolved : String) →
  CorpusWorld.requiredHorizon
    (claimToCitedSourceHorizon r status unresolved)
    ≡ CorpusWorld.citedSourceCorpusHorizon
claimHorizonIsCitedSourceCorpus r status unresolved = refl

------------------------------------------------------------------------
-- Correspondence is explicit and weaker than identity.
------------------------------------------------------------------------

data EntryCorrespondenceKind : Set where
  sameTopic : EntryCorrespondenceKind
  broaderTopic : EntryCorrespondenceKind
  narrowerTopic : EntryCorrespondenceKind
  overlappingTopic : EntryCorrespondenceKind
  historicalSuccessor : EntryCorrespondenceKind
  ambiguousMatch : EntryCorrespondenceKind

record EntryCorrespondence : Set where
  constructor entryCorrespondence
  field
    leftEntry : EncyclopediaEntryIdentity
    rightEntry : EncyclopediaEntryIdentity
    correspondenceKind : EntryCorrespondenceKind
    correspondenceEvidenceReference : String
open EntryCorrespondence public

data ClaimRelationship : Set where
  equivalentClaim : ClaimRelationship
  compatibleClaim : ClaimRelationship
  qualificationDifference : ClaimRelationship
  temporalDifference : ClaimRelationship
  contradictoryClaim : ClaimRelationship
  incomparableClaim : ClaimRelationship

record CorpusClaimComparison : Set where
  constructor corpusClaimComparison
  field
    leftClaim : CorpusClaimReceipt
    rightClaim : CorpusClaimReceipt
    relationship : ClaimRelationship
    comparisonEvidenceReference : String
open CorpusClaimComparison public

------------------------------------------------------------------------
-- Fail-closed semantic boundaries.
------------------------------------------------------------------------

data CorpusClaimReceiptIsWorldTruth : Set where
data EditorialAuthorityIsConsumerAuthority : Set where
data MatchingEntryTitleIsSameConcept : Set where
data CategoryPlacementIsSubclassFact : Set where
data CrossCorpusAgreementIsWorldTruth : Set where

corpusClaimReceiptDoesNotCreateWorldTruth :
  CorpusClaimReceiptIsWorldTruth → ⊥
corpusClaimReceiptDoesNotCreateWorldTruth ()

editorialAuthorityDoesNotCreateConsumerAuthority :
  EditorialAuthorityIsConsumerAuthority → ⊥
editorialAuthorityDoesNotCreateConsumerAuthority ()

matchingTitleDoesNotCreateConceptIdentity :
  MatchingEntryTitleIsSameConcept → ⊥
matchingTitleDoesNotCreateConceptIdentity ()

categoryPlacementDoesNotCreateSubclassFact :
  CategoryPlacementIsSubclassFact → ⊥
categoryPlacementDoesNotCreateSubclassFact ()

crossCorpusAgreementDoesNotCreateWorldTruth :
  CrossCorpusAgreementIsWorldTruth → ⊥
crossCorpusAgreementDoesNotCreateWorldTruth ()

record EncyclopediaCorpusBoundary : Set where
  constructor encyclopediaCorpusBoundary
  field
    editionIdentityIsFirstClass : Bool
    exactPassageCarrierIsFirstClass : Bool
    sourceAssertionCreatesWorldTruth : Bool
    editorialAuthorityAutomaticallyPaysConsumerAuthority : Bool
    matchingTitleCreatesConceptIdentity : Bool
    crossCorpusAgreementCreatesWorldTruth : Bool
    corpusClaimsEnterCitedSourceHorizon : Bool

canonicalEncyclopediaCorpusBoundary : EncyclopediaCorpusBoundary
canonicalEncyclopediaCorpusBoundary =
  encyclopediaCorpusBoundary
    true true false false false false true
