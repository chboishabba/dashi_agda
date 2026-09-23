module DASHI.Education.DigitalESDSearchToSourceAuditAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDStructuredSearchExact as Search
import DASHI.Education.DigitalESDSourceAuditAdmissionExact as Audit

------------------------------------------------------------------------
-- STRUCTURED SEARCH -> SOURCE AUDIT ADMISSION WELD
--
-- This owner does not manufacture a closed search, included study, or audit.
-- It only defines the final same-object carrier that a source must inhabit
-- before corpus synthesis:
--
--   transparent structured-search closure
--   + source-specific included-set lineage receipt
--   + source-indexed SourceAuditAdmission
--   -> CorpusAuditedSource source
--
-- External membership remains an observed/review-work fact represented by the
-- retained included-set/source-identity references. This module does not claim
-- those references are populated for the current review.
------------------------------------------------------------------------

record IncludedSourceLineage (source : Attr.AttributedSource) : Set where
  constructor included-source-lineage
  field
    searchClosure : Search.TransparentStructuredSearchClosureReceipt
    includedSetMemberReference : String
    includedSourceIdentityReference : String
    screeningDecisionReference : String
    structuredExtractionRowReference : String
    provenanceReceipt : Snowball.SourceRoleSnowballReceipt source
    sameObjectIdentityRetained : Bool
    sameObjectIdentityRetainedIsTrue : sameObjectIdentityRetained ≡ true

open IncludedSourceLineage public

mkIncludedSourceLineage :
  (source : Attr.AttributedSource) →
  Search.TransparentStructuredSearchClosureReceipt →
  String → String → String → String →
  IncludedSourceLineage source
mkIncludedSourceLineage source closure memberRef identityRef decisionRef extractionRef =
  included-source-lineage
    closure
    memberRef
    identityRef
    decisionRef
    extractionRef
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    true refl

record CorpusAuditedSource (source : Attr.AttributedSource) : Set where
  constructor corpus-audited-source
  field
    includedLineage : IncludedSourceLineage source
    auditAdmission : Audit.SourceAuditAdmission source

open CorpusAuditedSource public

mkCorpusAuditedSource :
  (source : Attr.AttributedSource) →
  IncludedSourceLineage source →
  Audit.SourceAuditAdmission source →
  CorpusAuditedSource source
mkCorpusAuditedSource source lineage admission =
  corpus-audited-source lineage admission

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data PreScreenCandidateCreatesCorpusAuditedSource : Set where
data SearchHitCreatesCorpusAuditedSource : Set where
data AuditAdmissionCreatesSearchLineage : Set where
data SearchLineageCreatesAuditAdmission : Set where
data IncludedSetReferenceCreatesSourceTruth : Set where
data CorpusAuditedSourceCreatesClaimAuthority : Set where

preScreenCandidateDoesNotCreateCorpusAuditedSource :
  PreScreenCandidateCreatesCorpusAuditedSource → ⊥
preScreenCandidateDoesNotCreateCorpusAuditedSource ()

searchHitDoesNotCreateCorpusAuditedSource :
  SearchHitCreatesCorpusAuditedSource → ⊥
searchHitDoesNotCreateCorpusAuditedSource ()

auditAdmissionDoesNotCreateSearchLineage :
  AuditAdmissionCreatesSearchLineage → ⊥
auditAdmissionDoesNotCreateSearchLineage ()

searchLineageDoesNotCreateAuditAdmission :
  SearchLineageCreatesAuditAdmission → ⊥
searchLineageDoesNotCreateAuditAdmission ()

includedSetReferenceDoesNotCreateSourceTruth :
  IncludedSetReferenceCreatesSourceTruth → ⊥
includedSetReferenceDoesNotCreateSourceTruth ()

corpusAuditedSourceDoesNotCreateClaimAuthority :
  CorpusAuditedSourceCreatesClaimAuthority → ⊥
corpusAuditedSourceDoesNotCreateClaimAuthority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SearchAuditWeldBoundary : Set where
  constructor search-audit-weld-boundary
  field
    searchLineageAndAuditRemainDistinct : Bool
    searchLineageAndAuditRemainDistinctIsTrue :
      searchLineageAndAuditRemainDistinct ≡ true
    sameSourceIndexedAcrossWeld : Bool
    sameSourceIndexedAcrossWeldIsTrue :
      sameSourceIndexedAcrossWeld ≡ true
    preScreenCandidateMayBypassScreening : Bool
    preScreenCandidateMayBypassScreeningIsFalse :
      preScreenCandidateMayBypassScreening ≡ false
    searchHitMayBypassAudit : Bool
    searchHitMayBypassAuditIsFalse :
      searchHitMayBypassAudit ≡ false

open SearchAuditWeldBoundary public

canonicalSearchAuditWeldBoundary : SearchAuditWeldBoundary
canonicalSearchAuditWeldBoundary = search-audit-weld-boundary
  true refl
  true refl
  false refl
  false refl

searchAuditWeldReading : String
searchAuditWeldReading =
  "A source reaches Digital-ESD corpus synthesis only through two independent same-object payments: retained inclusion/extraction lineage from a transparent structured-search closure and a source-indexed SourceAuditAdmission. Pre-screen discovery, search hits, included-set references, and audit completion do not manufacture one another or create claim authority."
