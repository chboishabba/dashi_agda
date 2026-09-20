module DASHI.Education.DigitalESDERICStudyInteropExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- REAL ERIC STUDY-METADATA INTEROP BOUNDARY
--
-- Runtime owner:
--   interop_scripts/digital_esd_eric.py
--
-- Input:
--   retained raw ERIC API JSON pages + per-query execution summaries
--
-- Output:
--   one stable metadata/abstract record per ERIC accession, retaining
--   cross-query membership and raw-page provenance.
--
-- This is deliberately before screening and before full-text/SensibLaw work.
------------------------------------------------------------------------

record ERICRawObservationProvenance : Set where
  constructor eric-raw-observation-provenance
  field
    queryId : String
    pageReference : String
    pageSha256 : String
    requestReference : String
    documentIndexReference : String

open ERICRawObservationProvenance public

record ERICParsedStudyMetadata : Set where
  constructor eric-parsed-study-metadata
  field
    ericId : String
    sourceIdentityReference : String

    title : String
    abstractText : String
    authorReference : String
    publicationYearReference : String
    publicationTypeReference : String
    subjectReference : String
    educationLevelReference : String
    sourceReference : String
    urlReference : String

    metadataSha256 : String
    metadataRevisionReference : String
    queryMembershipReference : String
    rawObservationProvenance : List ERICRawObservationProvenance

    metadataParsed : Bool
    metadataParsedIsTrue : metadataParsed ≡ true

    abstractPresent : Bool

    fullTextRetrieved : Bool
    fullTextRetrievedIsFalse : fullTextRetrieved ≡ false

    fullTextParsed : Bool
    fullTextParsedIsFalse : fullTextParsed ≡ false

    createsScreeningDecision : Bool
    createsScreeningDecisionIsFalse :
      createsScreeningDecision ≡ false

    createsSourceTruth : Bool
    createsSourceTruthIsFalse :
      createsSourceTruth ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open ERICParsedStudyMetadata public

record ERICStudyInteropBoundary : Set where
  constructor eric-study-interop-boundary
  field
    parsesRetainedERICExports : Bool
    parsesRetainedERICExportsIsTrue :
      parsesRetainedERICExports ≡ true

    preservesStableERICIdentity : Bool
    preservesStableERICIdentityIsTrue :
      preservesStableERICIdentity ≡ true

    preservesCrossQueryMembership : Bool
    preservesCrossQueryMembershipIsTrue :
      preservesCrossQueryMembership ≡ true

    verifiesRawPageDigests : Bool
    verifiesRawPageDigestsIsTrue :
      verifiesRawPageDigests ≡ true

    conflictingMetadataFailsClosed : Bool
    conflictingMetadataFailsClosedIsTrue :
      conflictingMetadataFailsClosed ≡ true

    metadataParsingIsFullTextParsing : Bool
    metadataParsingIsFullTextParsingIsFalse :
      metadataParsingIsFullTextParsing ≡ false

    abstractParsingIsFullTextParsing : Bool
    abstractParsingIsFullTextParsingIsFalse :
      abstractParsingIsFullTextParsing ≡ false

    fullTextAvailabilityMeansRetrieved : Bool
    fullTextAvailabilityMeansRetrievedIsFalse :
      fullTextAvailabilityMeansRetrieved ≡ false

    parserCreatesScreeningDecision : Bool
    parserCreatesScreeningDecisionIsFalse :
      parserCreatesScreeningDecision ≡ false

    parserCreatesSourceAuditAdmission : Bool
    parserCreatesSourceAuditAdmissionIsFalse :
      parserCreatesSourceAuditAdmission ≡ false

open ERICStudyInteropBoundary public

canonicalERICStudyInteropBoundary : ERICStudyInteropBoundary
canonicalERICStudyInteropBoundary =
  eric-study-interop-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

data ParsedMetadataCreatesScreeningDecision : Set where
data ParsedMetadataCreatesSourceTruth : Set where
data ParsedMetadataCreatesSourceAuditAdmission : Set where
data ParsedAbstractCountsAsFullTextParsing : Set where
data ERICFullTextAvailabilityCountsAsRetrievedArtifact : Set where
data QueryOverlapCreatesDuplicateStudyIdentity : Set where
data ConflictingMetadataMayBeSilentlyMerged : Set where
data SyntheticSLRFixtureCountsAsERICCorpus : Set where

parsedMetadataDoesNotCreateScreeningDecision :
  ParsedMetadataCreatesScreeningDecision → ⊥
parsedMetadataDoesNotCreateScreeningDecision ()

parsedMetadataDoesNotCreateSourceTruth :
  ParsedMetadataCreatesSourceTruth → ⊥
parsedMetadataDoesNotCreateSourceTruth ()

parsedMetadataDoesNotCreateSourceAuditAdmission :
  ParsedMetadataCreatesSourceAuditAdmission → ⊥
parsedMetadataDoesNotCreateSourceAuditAdmission ()

parsedAbstractDoesNotCountAsFullTextParsing :
  ParsedAbstractCountsAsFullTextParsing → ⊥
parsedAbstractDoesNotCountAsFullTextParsing ()

ericFullTextAvailabilityDoesNotCountAsRetrievedArtifact :
  ERICFullTextAvailabilityCountsAsRetrievedArtifact → ⊥
ericFullTextAvailabilityDoesNotCountAsRetrievedArtifact ()

queryOverlapDoesNotCreateDuplicateStudyIdentity :
  QueryOverlapCreatesDuplicateStudyIdentity → ⊥
queryOverlapDoesNotCreateDuplicateStudyIdentity ()

conflictingMetadataCannotBeSilentlyMerged :
  ConflictingMetadataMayBeSilentlyMerged → ⊥
conflictingMetadataCannotBeSilentlyMerged ()

syntheticSLRFixtureDoesNotCountAsERICCorpus :
  SyntheticSLRFixtureCountsAsERICCorpus → ⊥
syntheticSLRFixtureDoesNotCountAsERICCorpus ()

ericStudyInteropReading : String
ericStudyInteropReading =
  "Digital-ESD parses retained raw ERIC API pages into stable ERIC study-metadata records before screening. The parser verifies raw-page digests, preserves ERIC accession identity, cross-query memberships and raw provenance, and fails closed on conflicting normalized metadata for the same accession. Metadata/abstract parsing is not full-text parsing; ERIC full-text availability is not retrieval; parsed records do not create screening decisions, source truth or SourceAuditAdmission; and the synthetic 43,996-row SLR scale fixture is not the ERIC corpus."
