module DASHI.Interop.SLRCanonicalClaimProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSensibLawCandidateWorldAdapterExact as Adapter
import DASHI.Interop.SLRValidationRoadmapPromotionExact as Validation
import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as Claims
import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as Ibrahim

------------------------------------------------------------------------
-- Canonical claim projection from SLR CandidateWorldModel.
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_claim_projection.py
--   schema = slr-canonical-claim-projection-v2
--
-- Historical parser-sentence mappings remain useful candidate coverage.  The
-- tracked speaker-labelled primary transcript can additionally pay an exact
-- subspan weld only when source SHA, unique bounded phrase and candidate
-- source offsets all agree.  Neither route promotes the proposition as true.
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
    mappingReference : String
    sourceDigestReference : String
    status : ProjectionStatus
    sourcePaidClaimIdentity : Bool
    primarySpeakerAttributionPaid : Bool
    exactSubspanWeld : Bool
    historicalFixtureSpeakerUsedAsAuthority : Bool
    historicalFixtureRewritten : Bool
    semanticPromotion : Bool

open CanonicalClaimProjection public

c029Projection : CanonicalClaimProjection
c029Projection = canonicalClaimProjection
  "SLR candidate nodes overlapping the unique C029 primary-source phrase"
  "ABC730-2026-09-09-C029"
  "fixture parser-sentence coverage + same-source unique phrase/offset weld"
  "ABC primary transcript SHA 61c86754...408383"
  exactSubspanWeldPaid
  true true true false false false

c030Projection : CanonicalClaimProjection
c030Projection = canonicalClaimProjection
  "SLR candidate nodes overlapping the unique C030 primary-source phrase"
  "ABC730-2026-09-09-C030"
  "historical sentence candidate -> later labelled primary source -> exact source span"
  "ABC primary transcript SHA 61c86754...408383"
  exactSubspanWeldPaid
  true true true false false false

c032Projection : CanonicalClaimProjection
c032Projection = canonicalClaimProjection
  "SLR candidate nodes overlapping the unique C032 primary-source phrase"
  "ABC730-2026-09-09-C032"
  "historical likely speaker -> later labelled primary source -> exact source span"
  "ABC primary transcript SHA 61c86754...408383"
  exactSubspanWeldPaid
  true true true false false false

c033Projection : CanonicalClaimProjection
c033Projection = canonicalClaimProjection
  "SLR candidate nodes overlapping the unique C033 primary-source phrase"
  "ABC730-2026-09-09-C033"
  "historical sentence candidate -> later labelled primary source -> exact source span"
  "ABC primary transcript SHA 61c86754...408383"
  exactSubspanWeldPaid
  true true true false false false

projectionFrontier : List CanonicalClaimProjection
projectionFrontier = c029Projection ∷ c030Projection ∷ c032Projection ∷ c033Projection ∷ []

------------------------------------------------------------------------
-- Runtime boundary.
------------------------------------------------------------------------

record ClaimProjectionRuntimeBoundary : Set where
  constructor claimProjectionRuntimeBoundary
  field
    schemaReference : String
    targetWorldSchemaReference : String
    historicalMappingUsesExplicitClaimRefs : Bool
    historicalMappingUsesParserSentenceIds : Bool
    primaryMappingRequiresSameSourceSHA : Bool
    primaryMappingRequiresUniqueBoundedPhrase : Bool
    primaryMappingRequiresCandidateOffsets : Bool
    fuzzyTextMatchingUsed : Bool
    historicalFixtureSpeakerCreatesAuthority : Bool
    laterPrimaryReceiptMayPayAttribution : Bool
    laterPrimaryReceiptRewritesHistoricalState : Bool
    exactSubspanWeldDefaultPaid : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ClaimProjectionRuntimeBoundary public

canonicalClaimProjectionRuntimeBoundary : ClaimProjectionRuntimeBoundary
canonicalClaimProjectionRuntimeBoundary = claimProjectionRuntimeBoundary
  "slr-canonical-claim-projection-v2"
  "sl.candidate_world_model.v0_1"
  true true true true true false false true false false true false

------------------------------------------------------------------------
-- Snowball / WrongType firewalls.
------------------------------------------------------------------------

data SentenceCoverageMeansExactSubspan : Set where
data HistoricalFixtureSpeakerMeansVerifiedSpeaker : Set where
data PrimarySpeakerLabelMeansUnderlyingClaimTrue : Set where
data ClaimReferenceMeansClaimTruth : Set where
data TextSimilarityMayReplaceExplicitMapping : Set where
data QIDMayPayClaimTruth : Set where
data DeweyMayPayClaimTruth : Set where
data DOIMayPayClaimTruth : Set where
data LaterPrimaryReceiptMayRewriteHistoricalFixture : Set where

sentenceCoverageDoesNotPayExactSubspan : SentenceCoverageMeansExactSubspan → ⊥
sentenceCoverageDoesNotPayExactSubspan ()

historicalFixtureSpeakerDoesNotVerifySpeaker : HistoricalFixtureSpeakerMeansVerifiedSpeaker → ⊥
historicalFixtureSpeakerDoesNotVerifySpeaker ()

primarySpeakerDoesNotPromoteUnderlyingClaim : PrimarySpeakerLabelMeansUnderlyingClaimTrue → ⊥
primarySpeakerDoesNotPromoteUnderlyingClaim ()

claimReferenceDoesNotMeanTruth : ClaimReferenceMeansClaimTruth → ⊥
claimReferenceDoesNotMeanTruth ()

textSimilarityMayNotReplaceMapping : TextSimilarityMayReplaceExplicitMapping → ⊥
textSimilarityMayNotReplaceMapping ()

qidDoesNotPayClaimTruth : QIDMayPayClaimTruth → ⊥
qidDoesNotPayClaimTruth ()

deweyDoesNotPayClaimTruth : DeweyMayPayClaimTruth → ⊥
deweyDoesNotPayClaimTruth ()

doiDoesNotPayClaimTruth : DOIMayPayClaimTruth → ⊥
doiDoesNotPayClaimTruth ()

laterPrimaryDoesNotRewriteHistoricalFixture : LaterPrimaryReceiptMayRewriteHistoricalFixture → ⊥
laterPrimaryDoesNotRewriteHistoricalFixture ()

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

adapterReceiptAnchor : Adapter.SLRSensibLawWorldAdapterReceipt
adapterReceiptAnchor = Adapter.canonicalSLRSensibLawWorldAdapterReceipt

validationBoundaryAnchor : Validation.ValidationPromotionBoundary
validationBoundaryAnchor = Validation.canonicalValidationPromotionBoundary

ibrahimBoundaryAnchor : Ibrahim.SnowballAttributionBoundary
ibrahimBoundaryAnchor = Ibrahim.canonicalSnowballAttributionBoundary

c029ClaimAnchor : Claims.TranscriptClaim
c029ClaimAnchor = Claims.c029

c032ClaimAnchor : Claims.TranscriptClaim
c032ClaimAnchor = Claims.c032
