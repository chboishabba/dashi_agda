module DASHI.Wikimedia.SensibLawWikipediaIngestContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.SourceProvenanceExact as Source

------------------------------------------------------------------------
-- SENSIBLAW <-> NATIVE WIKIPEDIA INGEST CONTRACT
--
-- Existing runtime donor:
--   chboishabba/SensibLaw revision-locked Wikipedia pull/harness surfaces.
-- Future proof donor:
--   dashifine whole-Wikimedia parsing theorem/contract must be pinned by exact
--   declaration before DASHI claims that theorem here.
--
-- The contract is therefore useful now without overclaiming the future proof:
-- parser output remains tied to the exact Wikipedia revision and parser build.
------------------------------------------------------------------------

record SensibLawParserIdentity : Set where
  constructor sensibLawParserIdentity
  field
    parserRepository : String
    parserRevision : String
    parserContractReference : String
open SensibLawParserIdentity public

record ParsedWikipediaCarrier : Set where
  constructor parsedWikipediaCarrier
  field
    carrierReference : String
    carrierContentHash : String
    parserIdentity : SensibLawParserIdentity
    sourceRevision : Source.WikipediaRevisionReceipt
open ParsedWikipediaCarrier public

record ParseReceipt : Set where
  constructor parseReceipt
  field
    parsedCarrier : ParsedWikipediaCarrier
    inputRevisionMatched : Bool
    parserRevisionMatched : Bool
    outputHashPinned : Bool
    receiptReference : String
open ParseReceipt public

record CorpusShard : Set where
  constructor corpusShard
  field
    shardReference : String
    sourceManifestHash : String
    parserManifestHash : String
    outputManifestHash : String
open CorpusShard public

-- Parsing is structural extraction/projection, not semantic or authority
-- promotion.  Those obligations remain downstream PNF/source consumers.
data ParserSuccessIsWorldTruth : Set where
data ParsedCitationIsVerifiedAuthority : Set where
data ParsedWikipediaClaimIsWikidataStatement : Set where
data WholeCorpusPlanMeansWholeCorpusAlreadyProvedHere : Set where

parserSuccessDoesNotCreateWorldTruth : ParserSuccessIsWorldTruth → ⊥
parserSuccessDoesNotCreateWorldTruth ()

parsedCitationDoesNotCreateVerifiedAuthority : ParsedCitationIsVerifiedAuthority → ⊥
parsedCitationDoesNotCreateVerifiedAuthority ()

parsedWikipediaClaimDoesNotBecomeWikidataStatement :
  ParsedWikipediaClaimIsWikidataStatement → ⊥
parsedWikipediaClaimDoesNotBecomeWikidataStatement ()

wholeCorpusPlanIsNotWholeCorpusProof :
  WholeCorpusPlanMeansWholeCorpusAlreadyProvedHere → ⊥
wholeCorpusPlanIsNotWholeCorpusProof ()

record SensibLawWikipediaBoundary : Set where
  constructor sensiblaw-wikipedia-boundary
  field
    parserReceiptPinsRevision : Bool
    parserReceiptPinsParserVersion : Bool
    parserSuccessCreatesTruth : Bool
    parserSuccessCreatesSourceAuthority : Bool
    wholeCorpusProofPinnedInThisModule : Bool

canonicalSensibLawWikipediaBoundary : SensibLawWikipediaBoundary
canonicalSensibLawWikipediaBoundary =
  sensiblaw-wikipedia-boundary true true false false false
