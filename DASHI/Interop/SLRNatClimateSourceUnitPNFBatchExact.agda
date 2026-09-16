module DASHI.Interop.SLRNatClimateSourceUnitPNFBatchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRWikipediaArticlePNFWorldProducerExact as Article
import DASHI.Wikimedia.SensibLawNatClimateSLRFixtureExact as Nat

------------------------------------------------------------------------
-- NAT CLIMATE SOURCE-UNIT -> SPACY -> PNF BATCH
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py
--
-- The Nat climate tranche uses the same generic source-manifestation and PNF
-- producer ABI as Wikipedia article text.  Source units are processed as
-- independent fibres, retain revision/hash/source-role coordinates, and are
-- never collapsed into one mutually authoritative 30k-document object.
------------------------------------------------------------------------

record SourceUnitPNFBatchBoundary : Set where
  constructor sourceUnitPNFBatchBoundary
  field
    producerABIReference : String
    oneRecordPerSourceUnit : Bool
    sourceHashRequired : Bool
    revisionReferenceRequired : Bool
    trainedDependencyParserRequired : Bool
    parserModelReusedPerLanguage : Bool
    rawTextEmbeddedInManifest : Bool
    sourceUnitsMutuallyAuthoritative : Bool
    sourceRoleCreatesClaimTruth : Bool
    parserOutputCreatesOntologyTruth : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open SourceUnitPNFBatchBoundary public

canonicalSourceUnitPNFBatchBoundary : SourceUnitPNFBatchBoundary
canonicalSourceUnitPNFBatchBoundary =
  sourceUnitPNFBatchBoundary
    "sensiblaw-integrated-semantic-producer-compatible-v1"
    true true true true true
    false false false false true false

record NatClimateBatchCoordinate : Set where
  constructor natClimateBatchCoordinate
  field
    sourceUnitReference : String
    sourceFamilyReference : String
    languageReference : String
    revisionReference : String
    sourceTextHashReference : String
    parserReceiptReference : String
    pnfCandidateManifestReference : String
    qidWeldReference : String
    consumerResidualReference : String
    migrationApproved : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open NatClimateBatchCoordinate public

canonicalNatClimateBatchCoordinate : NatClimateBatchCoordinate
canonicalNatClimateBatchCoordinate =
  natClimateBatchCoordinate
    "unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01"
    "nat-climate:p5991-p14143"
    "source-language"
    "provided_snapshot_2026-04-01"
    "source_text_sha256"
    "spacy-trained-dependency-receipt"
    "source-unit-pnf-record"
    "qid/pid-weld-still-separate"
    "consumer-relative-residual"
    false true false

articleProducerAnchor : Article.GenericTextWorldProducerABI
articleProducerAnchor = Article.canonicalGenericTextWorldProducerABI

natFixtureReference : String
natFixtureReference = "SensibLawNatClimateSLRFixtureExact.natSourceUnit"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ThirtyKSourceUnitsBecomeOneAuthority : Set where
data SourceRoleCreatesTruth : Set where
data ParserOutputCreatesOntologyTruth : Set where
data NatPNFMeansMigrationApproved : Set where
data BatchSizeCreatesPromotion : Set where

thirtyKUnitsRemainDistinctFibres : ThirtyKSourceUnitsBecomeOneAuthority → ⊥
thirtyKUnitsRemainDistinctFibres ()

sourceRoleDoesNotCreateTruth : SourceRoleCreatesTruth → ⊥
sourceRoleDoesNotCreateTruth ()

parserOutputDoesNotCreateOntologyTruth : ParserOutputCreatesOntologyTruth → ⊥
parserOutputDoesNotCreateOntologyTruth ()

natPNFDoesNotApproveMigration : NatPNFMeansMigrationApproved → ⊥
natPNFDoesNotApproveMigration ()

batchSizeDoesNotCreatePromotion : BatchSizeCreatesPromotion → ⊥
batchSizeDoesNotCreatePromotion ()
