module DASHI.Law.SensibLawImmutableLegalResearchWorldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawParsedAuthorityReasoningGraphExact as Reasoning

------------------------------------------------------------------------
-- IMMUTABLE LEGAL RESEARCH MEMORY
--
-- Acquired and parsed sources accumulate as revision-scoped immutable receipts.
-- Conclusions may later change, but prior source/provenance/reasoning receipts are
-- never silently rewritten to match the new conclusion.
------------------------------------------------------------------------

record ImmutableSourceRevision : Set₁ where
  constructor immutableSourceRevision
  field
    sourceRevisionReference : String
    canonicalBytesDigestReference : String
    canonicalTextDigestReference : String
    providerReceiptReference : String
    jurisdictionReference : String
    sourceRoleReference : String
    authorityCandidateReference : String
    parsedPNFReference : String
    citationTopologyReference : String
    assessmentReceiptReferences : List String
    revisionImmutabilityReceipt : Set

open ImmutableSourceRevision public

record LegalResearchWorldSnapshot : Set₁ where
  constructor legalResearchWorldSnapshot
  field
    snapshotReference : String
    sourceRevisions : List ImmutableSourceRevision
    reasoningDeltaReferences : List String
    queryVocabularyReferences : List String
    authorityNeighbourhoodReferences : List String
    iterationReceiptReferences : List String
    openFrontierReferences : List String

open LegalResearchWorldSnapshot public

record AppendOnlyResearchExtension
    (prior posterior : LegalResearchWorldSnapshot) : Set₁ where
  constructor appendOnlyResearchExtension
  field
    allPriorSourceRevisionsRetainedReceipt : Set
    allPriorReasoningDeltasRetainedReceipt : Set
    allPriorIterationReceiptsRetainedReceipt : Set
    newlyAddedSourceRevisionReferences : List String
    newlyAddedReasoningDeltaReferences : List String
    newlyAddedVocabularyReferences : List String
    noSilentHistoricalRewriteReceipt : Set
    extensionReference : String

open AppendOnlyResearchExtension public

record ReasoningDeltaAdmission : Set₁ where
  constructor reasoningDeltaAdmission
  field
    sourceRevision : ImmutableSourceRevision
    reasoningDelta : Reasoning.ParsedAuthorityReasoningDelta
    sameDocumentReceipt : Set
    sameSourceRevisionReceipt : Set
    candidateOnlyReceipt : Set
    admissionReference : String

open ReasoningDeltaAdmission public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NewConclusionMayRewriteOldReceipt : Set where
data SameTextDigestMeansSameLegalEffect : Set where
data MoreStoredAuthoritiesMeansProofClosed : Set where
data AuthorityCandidateMeansCurrentAuthority : Set where

newConclusionDoesNotRewriteOldReceipt : NewConclusionMayRewriteOldReceipt → ⊥
newConclusionDoesNotRewriteOldReceipt ()

sameTextDoesNotMeanSameLegalEffect : SameTextDigestMeansSameLegalEffect → ⊥
sameTextDoesNotMeanSameLegalEffect ()

moreStoredAuthoritiesDoNotCloseProof : MoreStoredAuthoritiesMeansProofClosed → ⊥
moreStoredAuthoritiesDoNotCloseProof ()

authorityCandidateDoesNotMeanCurrentAuthority : AuthorityCandidateMeansCurrentAuthority → ⊥
authorityCandidateDoesNotMeanCurrentAuthority ()

record ImmutableResearchWorldBoundary : Set where
  constructor immutableResearchWorldBoundary
  field
    sourceRevisionsAreImmutable : Bool
    sourceRevisionsAreImmutableIsTrue : sourceRevisionsAreImmutable ≡ true
    researchMemoryIsAppendOnly : Bool
    researchMemoryIsAppendOnlyIsTrue : researchMemoryIsAppendOnly ≡ true
    conclusionsMayBeNonMonotone : Bool
    conclusionsMayBeNonMonotoneIsTrue : conclusionsMayBeNonMonotone ≡ true
    priorReceiptsMayBeSilentlyRewritten : Bool
    priorReceiptsMayBeSilentlyRewrittenIsFalse : priorReceiptsMayBeSilentlyRewritten ≡ false

canonicalImmutableResearchWorldBoundary : ImmutableResearchWorldBoundary
canonicalImmutableResearchWorldBoundary =
  immutableResearchWorldBoundary true refl true refl true refl false refl
