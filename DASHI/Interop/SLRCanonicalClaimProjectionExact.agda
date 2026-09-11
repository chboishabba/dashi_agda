module DASHI.Interop.SLRCanonicalClaimProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSensibLawCandidateWorldAdapterExact as Adapter
import DASHI.Interop.SLRValidationRoadmapPromotionExact as Validation
import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as Claims

------------------------------------------------------------------------
-- Canonical claim projection from SLR CandidateWorldModel.
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_claim_projection.py
--   schema = slr-canonical-claim-projection-v1
--
-- The mapping basis is an explicit repo fixture carrying canonical claim refs
-- and parser sentence ids.  It is not fuzzy text similarity.  Fused parser
-- sentences may project to more than one canonical claim; those projections
-- remain candidate/conflicted until an exact labelled alignment or cut receipt
-- pays the subspan weld.
------------------------------------------------------------------------

data ProjectionStatus : Set where
  exactClaimReference : ProjectionStatus
  candidateSentenceCoverage : ProjectionStatus
  conflictedSentenceCoverage : ProjectionStatus
  exactSubspanWeldPaid : ProjectionStatus
  exactSubspanWeldUnpaid : ProjectionStatus

record CanonicalClaimProjection : Set where
  constructor canonicalClaimProjection
  field
    discourseNodeReference : String
    canonicalClaimReference : String
    parserSentenceReference : String
    mappingFixtureReference : String
    status : ProjectionStatus
    sourcePaidClaimIdentity : Bool
    exactSubspanWeld : Bool
    fixtureSpeakerStatusUsedAsAuthority : Bool
    semanticPromotion : Bool

open CanonicalClaimProjection public

c029Coverage : CanonicalClaimProjection
c029Coverage = canonicalClaimProjection
  "SLR discourse nodes in parser sentences 41/42"
  "ABC730-2026-09-09-C029"
  "spaCy-41,spaCy-42"
  "fixtures/slr/abc730-west-bank-sanctions-2026-09-09-speaker-resolution.jsonl"
  conflictedSentenceCoverage
  true false false false

c030Coverage : CanonicalClaimProjection
c030Coverage = canonicalClaimProjection
  "SLR discourse nodes in parser sentences 42/43"
  "ABC730-2026-09-09-C030"
  "spaCy-42,spaCy-43"
  "fixtures/slr/abc730-west-bank-sanctions-2026-09-09-speaker-resolution.jsonl"
  conflictedSentenceCoverage
  true false false false

c032Coverage : CanonicalClaimProjection
c032Coverage = canonicalClaimProjection
  "SLR discourse nodes in parser sentences 44/45"
  "ABC730-2026-09-09-C032"
  "spaCy-44,spaCy-45"
  "fixtures/slr/abc730-west-bank-sanctions-2026-09-09-speaker-resolution.jsonl"
  conflictedSentenceCoverage
  true false false false

c033Coverage : CanonicalClaimProjection
c033Coverage = canonicalClaimProjection
  "SLR discourse nodes in parser sentences 45/46"
  "ABC730-2026-09-09-C033"
  "spaCy-45,spaCy-46"
  "fixtures/slr/abc730-west-bank-sanctions-2026-09-09-speaker-resolution.jsonl"
  conflictedSentenceCoverage
  true false false false

projectionFrontier : List CanonicalClaimProjection
projectionFrontier = c029Coverage ∷ c030Coverage ∷ c032Coverage ∷ c033Coverage ∷ []

------------------------------------------------------------------------
-- Runtime contract.
------------------------------------------------------------------------

record ClaimProjectionRuntimeBoundary : Set where
  constructor claimProjectionRuntimeBoundary
  field
    schemaReference : String
    targetWorldSchemaReference : String
    mappingUsesExplicitClaimRefs : Bool
    mappingUsesParserSentenceIds : Bool
    fuzzyTextMatchingUsed : Bool
    staleFixtureSpeakerStatusCreatesAuthority : Bool
    fusedSentenceMayProjectToMultipleClaims : Bool
    exactSubspanWeldDefaultPaid : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ClaimProjectionRuntimeBoundary public

canonicalClaimProjectionRuntimeBoundary : ClaimProjectionRuntimeBoundary
canonicalClaimProjectionRuntimeBoundary = claimProjectionRuntimeBoundary
  "slr-canonical-claim-projection-v1"
  "sl.candidate_world_model.v0_1"
  true true false false true false true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SentenceCoverageMeansExactSubspan : Set where
data FixtureSpeakerCandidateMeansVerifiedSpeaker : Set where
data ClaimReferenceMeansClaimTruth : Set where
data TextSimilarityMayReplaceExplicitMapping : Set where
data MultipleClaimCoverageMayBeSilentlyCollapsed : Set where

sentenceCoverageDoesNotPayExactSubspan : SentenceCoverageMeansExactSubspan → ⊥
sentenceCoverageDoesNotPayExactSubspan ()

fixtureSpeakerCandidateDoesNotVerifySpeaker :
  FixtureSpeakerCandidateMeansVerifiedSpeaker → ⊥
fixtureSpeakerCandidateDoesNotVerifySpeaker ()

claimReferenceDoesNotMeanTruth : ClaimReferenceMeansClaimTruth → ⊥
claimReferenceDoesNotMeanTruth ()

textSimilarityMayNotReplaceMapping : TextSimilarityMayReplaceExplicitMapping → ⊥
textSimilarityMayNotReplaceMapping ()

multipleCoverageMayNotCollapse : MultipleClaimCoverageMayBeSilentlyCollapsed → ⊥
multipleCoverageMayNotCollapse ()

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

adapterBoundaryAnchor : Adapter.SLRSensibLawWorldAdapterBoundary
adapterBoundaryAnchor = Adapter.canonicalSLRSensibLawWorldAdapterBoundary

validationBoundaryAnchor : Validation.ValidationPromotionBoundary
validationBoundaryAnchor = Validation.canonicalValidationPromotionBoundary

canonicalClaimLedgerReference : String
canonicalClaimLedgerReference = "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact"
