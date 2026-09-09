module DASHI.Cognition.PNF.SensibLawOALCLegislationParserInputContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- OALC LEGISLATION PARSER INPUT CONTRACT
--
-- Runtime parity target for SLR's local Open Australian Legal Corpus path.
-- The two supplied operator inputs are:
--   1. local corpus.jsonl path;
--   2. pinned immutable corpus revision reference.
--
-- Exact legislation records are then retained as source observations and may
-- be section-sliced for spaCy/PNF.  OALC's latest-known NSW legislation text is
-- parser-admissible, but it does not by itself establish that the same text was
-- in force on Cullen's historical date 2017-01-26.
------------------------------------------------------------------------

data OALCTemporalCoverage : Set where
  latestKnownOnly : OALCTemporalCoverage
  historicallyVerified : OALCTemporalCoverage

record PinnedOALCCorpusInput : Set where
  constructor pinned-oalc-corpus-input
  field
    corpusJSONLRef : String
    corpusRevisionRef : String
    immutableRevisionEvidenceRef : String

open PinnedOALCCorpusInput public

record OALCLegislationDocumentReceipt
    (input : PinnedOALCCorpusInput) : Set where
  constructor oalc-legislation-document-receipt
  field
    citation : String
    versionId : String
    sourceRef : String
    jurisdictionRef : String
    documentTypeRef : String
    canonicalTextDigest : String
    localArtifactRef : String
    temporalCoverage : OALCTemporalCoverage
    receiptAuthority : String

open OALCLegislationDocumentReceipt public

record OALCSectionSliceReceipt
    {input : PinnedOALCCorpusInput}
    (parent : OALCLegislationDocumentReceipt input) : Set where
  constructor oalc-section-slice-receipt
  field
    sectionRef : String
    sliceStart : Nat
    sliceEnd : Nat
    sliceDigest : String
    sliceArtifactRef : String
    sourcePreservingProjectionRef : String
    parserAuthority : String

open OALCSectionSliceReceipt public

record OALCParserHandoff
    {input : PinnedOALCCorpusInput}
    {parent : OALCLegislationDocumentReceipt input}
    (slice : OALCSectionSliceReceipt parent) : Set where
  constructor oalc-parser-handoff
  field
    corpusRevisionRetained : String
    parentVersionRetained : String
    parentDigestRetained : String
    sliceDigestRetained : String
    parserAuthorityRetained : String

open OALCParserHandoff public

------------------------------------------------------------------------
-- Historical equivalence is a distinct source coordinate.
------------------------------------------------------------------------

record HistoricalTextEquivalenceReceipt
    {input : PinnedOALCCorpusInput}
    (parent : OALCLegislationDocumentReceipt input)
    (dateRef : String) : Set where
  constructor historical-text-equivalence-receipt
  field
    historicalSourceRef : String
    historicalRevisionRef : String
    equivalenceEvidenceRef : String

------------------------------------------------------------------------
-- Cullen bounded fixture identifiers.
------------------------------------------------------------------------

cullenCivilLiabilityActCitation : String
cullenCivilLiabilityActCitation = "Civil Liability Act 2002 (NSW)"

cullenVicariousLiabilityActCitation : String
cullenVicariousLiabilityActCitation =
  "Law Reform (Vicarious Liability) Act 1983 (NSW)"

cullenHistoricalDate : String
cullenHistoricalDate = "2017-01-26"

cullenCivilLiabilitySections : String
cullenCivilLiabilitySections = "5A,5B,5C,5D,43A"

cullenVicariousLiabilitySections : String
cullenVicariousLiabilitySections = "6,7,8"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CorpusPathCreatesSourceAuthority : Set where
data PinnedRevisionCreatesLegalAuthority : Set where
data OALCRecordCreatesHistoricalEquivalence : Set where
data LatestKnownOnlyPaysHistoricalDate : Set where
data ParserHandoffCreatesAtomicGate : Set where
data PNFObservationCreatesLegalApplicability : Set where
data CurrentTextMaySilentlyReplaceHistoricalText : Set where

corpusPathDoesNotCreateAuthority : CorpusPathCreatesSourceAuthority → ⊥
corpusPathDoesNotCreateAuthority ()

pinnedRevisionDoesNotCreateAuthority : PinnedRevisionCreatesLegalAuthority → ⊥
pinnedRevisionDoesNotCreateAuthority ()

oalcRecordDoesNotCreateHistoricalEquivalence :
  OALCRecordCreatesHistoricalEquivalence → ⊥
oalcRecordDoesNotCreateHistoricalEquivalence ()

latestKnownOnlyDoesNotPayHistoricalDate :
  LatestKnownOnlyPaysHistoricalDate → ⊥
latestKnownOnlyDoesNotPayHistoricalDate ()

parserHandoffDoesNotCreateAtomicGate : ParserHandoffCreatesAtomicGate → ⊥
parserHandoffDoesNotCreateAtomicGate ()

pnfObservationDoesNotCreateApplicability :
  PNFObservationCreatesLegalApplicability → ⊥
pnfObservationDoesNotCreateApplicability ()

currentTextCannotSilentlyReplaceHistoricalText :
  CurrentTextMaySilentlyReplaceHistoricalText → ⊥
currentTextCannotSilentlyReplaceHistoricalText ()

record OALCLegislationParserInputBoundary : Set where
  constructor oalc-legislation-parser-input-boundary
  field
    localCorpusPathRequired : Bool
    pinnedRevisionRequired : Bool
    exactLegislationRecordRequired : Bool
    sourcePreservingSliceRequired : Bool
    latestKnownTextParserAdmissible : Bool
    latestKnownTextPaysHistoricalEquivalence : Bool
    parserCreatesLegalAuthority : Bool
    parserCreatesAtomicGate : Bool

canonicalOALCLegislationParserInputBoundary :
  OALCLegislationParserInputBoundary
canonicalOALCLegislationParserInputBoundary =
  oalc-legislation-parser-input-boundary
    true true true true true false false false
