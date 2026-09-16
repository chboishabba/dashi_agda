module DASHI.Interop.SLRGWBCandidateWorldProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- GWB SLR -> SENSIBLAW CANDIDATE WORLD PROJECTION
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_gwb_candidate_world.py
--   tools/slr-discourse-reconstruct/run_gwb_candidate_world.sh
--
-- Inputs are certification/projection receipts only.  Raw/projected corpus text
-- is deliberately not embedded in the CandidateWorldModel artifact.
------------------------------------------------------------------------

record GWBCertifiedProjectionSurface : Set where
  constructor gwbCertifiedProjectionSurface
  field
    certificationSchema : String
    projectionSchema : String
    profileReference : String
    documentCount : Nat
    sentenceCount : Nat
    paragraphCount : Nat
    sourceFamilyCount : Nat
    directReferenceParityFailures : Nat
    publicationOccurred : Bool

open GWBCertifiedProjectionSurface public

canonicalGWBCertifiedProjectionSurface : GWBCertifiedProjectionSurface
canonicalGWBCertifiedProjectionSurface = gwbCertifiedProjectionSurface
  "sensiblaw.gwb-full-certification-receipt.v0_1"
  "sensiblaw.gwb-source-projection.v0_1"
  "tranche-profile:gwb:v0_1"
  10 41134 12742 2 0 false

record GWBCandidateWorldBoundary : Set where
  constructor gwbCandidateWorldBoundary
  field
    targetSchema : String
    laneFamily : String
    sourceMode : String
    sentenceCandidates : Nat
    sentenceAdjacencyRelations : Nat
    provenanceDocuments : Nat
    rawTextEmbedded : Bool
    projectedTextEmbedded : Bool
    canonicalClaimIdentityAttached : Bool
    speakerQuoteGoldAttached : Bool
    worldConstraintsAttached : Bool
    candidateOnly : Bool
    semanticPromotion : Bool
    claimTruthPromoted : Bool

open GWBCandidateWorldBoundary public

canonicalGWBCandidateWorldBoundary : GWBCandidateWorldBoundary
canonicalGWBCandidateWorldBoundary = gwbCandidateWorldBoundary
  "sl.candidate_world_model.v0_1"
  "slr_document_corpus"
  "gwb_certified_projection_receipt"
  41134 41124 10
  false false false false false true false false

------------------------------------------------------------------------
-- What this pays.
------------------------------------------------------------------------

record GWBProjectionPayment : Set where
  constructor gwbProjectionPayment
  field
    certifiedSentenceIdentityRetained : Bool
    documentBoundariesRetained : Bool
    sourceProjectionHashesRetained : Bool
    sentenceAdjacencyRetained : Bool
    sourceFamilyCoordinatesRetained : Bool
    directReferenceParityImported : Bool
    canonicalClaimSemanticsPaid : Bool
    discourseSpeakerSemanticsPaid : Bool
    causalRelationSemanticsPaid : Bool
    worldTruthPaid : Bool

open GWBProjectionPayment public

canonicalGWBProjectionPayment : GWBProjectionPayment
canonicalGWBProjectionPayment = gwbProjectionPayment
  true true true true true true
  false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CertifiedSentenceMeansCanonicalClaim : Set where
data SentenceAdjacencyMeansDiscourseRelation : Set where
data SentenceAdjacencyMeansCausalRelation : Set where
data SourceHashMeansSourceAuthority : Set where
data GWBParityMeansWorldTruth : Set where
data MissingGoldMayBeSynthesised : Set where
data CandidateWorldMayEmbedRetainedBooks : Set where

certifiedSentenceDoesNotCreateClaim : CertifiedSentenceMeansCanonicalClaim → ⊥
certifiedSentenceDoesNotCreateClaim ()

adjacencyDoesNotCreateDiscourseRelation : SentenceAdjacencyMeansDiscourseRelation → ⊥
adjacencyDoesNotCreateDiscourseRelation ()

adjacencyDoesNotCreateCausation : SentenceAdjacencyMeansCausalRelation → ⊥
adjacencyDoesNotCreateCausation ()

sourceHashDoesNotCreateAuthority : SourceHashMeansSourceAuthority → ⊥
sourceHashDoesNotCreateAuthority ()

parityDoesNotCreateWorldTruth : GWBParityMeansWorldTruth → ⊥
parityDoesNotCreateWorldTruth ()

missingGoldMayNotBeSynthesised : MissingGoldMayBeSynthesised → ⊥
missingGoldMayNotBeSynthesised ()

candidateWorldMayNotEmbedRetainedBooks : CandidateWorldMayEmbedRetainedBooks → ⊥
candidateWorldMayNotEmbedRetainedBooks ()
