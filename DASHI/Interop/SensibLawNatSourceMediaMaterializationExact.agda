module DASHI.Interop.SensibLawNatSourceMediaMaterializationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source
import DASHI.Interop.SensibLawNatSourcePropositionVerificationExact as Verify

------------------------------------------------------------------------
-- PERSISTED SOURCE MEDIA: BYTES -> CANONICAL TEXT -> CANDIDATE SPAN
--
-- Runtime counterpart:
--
--   fetched bytes
--     -> SHA-256-addressed persisted artifact
--     -> digest re-verification on read
--     -> existing PDF/HTML media adapter
--     -> canonical text with page/character anchors
--     -> candidate evidence spans for one exact proposition demand
--
-- Candidate spans are search/refinement objects only.  Quantity/year/scope
-- co-occurrence is not proposition verification and cannot pay source support.
------------------------------------------------------------------------

data SourceMediaKind : Set where
  pdfMedia : SourceMediaKind
  htmlMedia : SourceMediaKind
  unsupportedMedia : SourceMediaKind

record PersistedSourceArtifact
    {residual : Source.NatSourceSupportResidual}
    {demand : Source.SourceFetchDemand residual}
    (fetchReceipt : Source.SourceFetchReceipt demand) : Set where
  constructor persistedSourceArtifact
  field
    sourceFetchReceiptReference : String
    contentDigest : String
    artifactRelativePath : String
    contentWasAcquired : Source.contentAcquired fetchReceipt ≡ true
    contentIntegrityWasObserved :
      Source.contentIntegrityObserved fetchReceipt ≡ true
    artifactPersisted : Bool
    artifactPersistedIsTrue : artifactPersisted ≡ true
    bytesReverifiedOnRead : Bool
    bytesReverifiedOnReadIsTrue : bytesReverifiedOnRead ≡ true
open PersistedSourceArtifact public

record CanonicalSourceMaterialization
    {residual : Source.NatSourceSupportResidual}
    {demand : Source.SourceFetchDemand residual}
    {fetchReceipt : Source.SourceFetchReceipt demand}
    (artifact : PersistedSourceArtifact fetchReceipt) : Set where
  constructor canonicalSourceMaterialization
  field
    observedSourceFetchReceiptReference : String
    observedSourceFetchReceiptIsExact :
      observedSourceFetchReceiptReference ≡ sourceFetchReceiptReference artifact
    observedContentDigest : String
    observedContentDigestIsExact : observedContentDigest ≡ contentDigest artifact
    mediaKind : SourceMediaKind
    canonicalTextDigest : String
    canonicalTextRelativePath : String
    pageAnchorsPreserved : Bool
    pageAnchorsPreservedIsTrue : pageAnchorsPreserved ≡ true
    characterAnchorsPreserved : Bool
    characterAnchorsPreservedIsTrue : characterAnchorsPreserved ≡ true
    propositionSupportEvaluated : Bool
    propositionSupportEvaluatedIsFalse : propositionSupportEvaluated ≡ false
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
    authorityEvaluated : Bool
    authorityEvaluatedIsFalse : authorityEvaluated ≡ false
open CanonicalSourceMaterialization public

record EvidenceSpanCandidate
    {residual : Source.NatSourceSupportResidual}
    {verificationDemand : Verify.SourceVerificationDemand residual}
    {fetchDemand : Source.SourceFetchDemand residual}
    {fetchReceipt : Source.SourceFetchReceipt fetchDemand}
    {artifact : PersistedSourceArtifact fetchReceipt}
    (materialization : CanonicalSourceMaterialization artifact) : Set where
  constructor evidenceSpanCandidate
  field
    verificationDemandReference : String
    verificationDemandIsExact :
      verificationDemandReference ≡ Verify.demandReference verificationDemand
    sourceArtifactReceiptReference : String
    sourceArtifactReceiptIsExact :
      sourceArtifactReceiptReference ≡
      Verify.sourceArtifactReceiptReference verificationDemand
    sourceArtifactMatchesMaterialization :
      sourceArtifactReceiptReference ≡
      observedSourceFetchReceiptReference materialization
    canonicalTextDigest : String
    canonicalTextDigestIsExact :
      canonicalTextDigest ≡
      CanonicalSourceMaterialization.canonicalTextDigest materialization
    evidenceLocator : String
    quantityAnchorObserved : Bool
    quantityAnchorObservedIsTrue : quantityAnchorObserved ≡ true
    yearCueObserved : Bool
    scopeCueObserved : Bool
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    propositionSupportEvaluated : Bool
    propositionSupportEvaluatedIsFalse : propositionSupportEvaluated ≡ false
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
    semanticPromotionPerformed : Bool
    semanticPromotionPerformedIsFalse : semanticPromotionPerformed ≡ false
open EvidenceSpanCandidate public

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data PersistedBytesPaySourceSupport : Set where
data CanonicalTextPaysSourceSupport : Set where
data CandidateSpanPaysSourceSupport : Set where
data CueCooccurrenceProvesSupport : Set where
data MissingQuantityAnchorProvesContradiction : Set where
data MaterializationCreatesAuthority : Set where

persistedBytesDoNotPaySourceSupport : PersistedBytesPaySourceSupport → ⊥
persistedBytesDoNotPaySourceSupport ()

canonicalTextDoesNotPaySourceSupport : CanonicalTextPaysSourceSupport → ⊥
canonicalTextDoesNotPaySourceSupport ()

candidateSpanDoesNotPaySourceSupport : CandidateSpanPaysSourceSupport → ⊥
candidateSpanDoesNotPaySourceSupport ()

cueCooccurrenceDoesNotProveSupport : CueCooccurrenceProvesSupport → ⊥
cueCooccurrenceDoesNotProveSupport ()

missingQuantityAnchorDoesNotProveContradiction :
  MissingQuantityAnchorProvesContradiction → ⊥
missingQuantityAnchorDoesNotProveContradiction ()

materializationDoesNotCreateAuthority : MaterializationCreatesAuthority → ⊥
materializationDoesNotCreateAuthority ()

record NatSourceMediaMaterializationBoundary : Set where
  constructor nat-source-media-materialization-boundary
  field
    fetchedBodiesMustBePersistedForReplay : Bool
    persistedBytesReverifiedAgainstDigest : Bool
    canonicalTextReusesExistingMediaAdapters : Bool
    onePhysicalArtifactMayServeManyResiduals : Bool
    pageCharacterEvidenceLocatorsPreserved : Bool
    candidateSpansAreSearchOnly : Bool
    candidateSpanPaysSupport : Bool
    cueCooccurrenceProvesSupport : Bool
    missingQuantityAnchorCreatesNegativeEvidence : Bool
    materializationCreatesAuthority : Bool
    semanticPromotionCreatedByMaterialization : Bool

canonicalNatSourceMediaMaterializationBoundary :
  NatSourceMediaMaterializationBoundary
canonicalNatSourceMediaMaterializationBoundary =
  nat-source-media-materialization-boundary
    true true true true true true false false false false false
