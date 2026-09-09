module DASHI.Cognition.PNF.SensibLawOALCLegislationParserInputContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- OALC LEGISLATION SOURCE / PARSER CONTRACT
--
-- corpus.jsonl is an optional provider implementation detail, not an ITIR
-- semantic input.  LegalFollow identifies the exact source demand; a governed
-- OALC provider resolves and retains the document; only that retained receipt
-- is eligible for source-preserving section slicing and spaCy/PNF.
--
--   LegalFollow source demand
--     -> governed OALC resolution
--     -> retained exact document receipt
--     -> section slice receipt
--     -> PNF handoff.
--
-- OALC latest-known text remains parser-admissible while historical equivalence
-- to Cullen's 2017 date remains an independent source coordinate.
------------------------------------------------------------------------

data OALCTemporalCoverage : Set where
  latestKnownOnly : OALCTemporalCoverage
  historicallyVerified : OALCTemporalCoverage

record OALCDatasetSelection : Set where
  constructor oalc-dataset-selection
  field
    datasetRef : String
    configRef : String
    splitRef : String
    corpusRevisionRef : String
    revisionPinEvidenceRef : String

open OALCDatasetSelection public

record OALCLegislationSourceDemand : Set where
  constructor oalc-legislation-source-demand
  field
    legalFollowDemandRef : String
    consumerRef : String
    citation : String
    jurisdictionRef : String
    sourceRoleRef : String
    authorityLevelRef : String
    providerProfileRef : String
    requestedTemporalRef : String

open OALCLegislationSourceDemand public

record OALCResolvedDocumentReceipt
    (dataset : OALCDatasetSelection)
    (demand : OALCLegislationSourceDemand) : Set where
  constructor oalc-resolved-document-receipt
  field
    resolvedCitation : String
    versionId : String
    sourceRef : String
    resolvedJurisdictionRef : String
    documentTypeRef : String
    canonicalTextDigest : String
    localArtifactRef : String
    temporalCoverage : OALCTemporalCoverage
    networkRequestCountRef : String
    receiptAuthority : String
    exactDemandRelationshipRef : String

open OALCResolvedDocumentReceipt public

record OALCSectionSliceReceipt
    {dataset : OALCDatasetSelection}
    {demand : OALCLegislationSourceDemand}
    (parent : OALCResolvedDocumentReceipt dataset demand) : Set where
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
    {dataset : OALCDatasetSelection}
    {demand : OALCLegislationSourceDemand}
    {parent : OALCResolvedDocumentReceipt dataset demand}
    (slice : OALCSectionSliceReceipt parent) : Set where
  constructor oalc-parser-handoff
  field
    legalFollowDemandRetained : String
    corpusRevisionRetained : String
    parentVersionRetained : String
    parentDigestRetained : String
    sliceDigestRetained : String
    parserAuthorityRetained : String

open OALCParserHandoff public

------------------------------------------------------------------------
-- Historical equivalence remains distinct.
------------------------------------------------------------------------

record HistoricalTextEquivalenceReceipt
    {dataset : OALCDatasetSelection}
    {demand : OALCLegislationSourceDemand}
    (parent : OALCResolvedDocumentReceipt dataset demand)
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

data LocalCorpusPathIsSemanticRequirement : Set where
data LegalFollowDemandCreatesSourceAuthority : Set where
data ProviderResolutionCreatesLegalAuthority : Set where
data OALCRecordCreatesHistoricalEquivalence : Set where
data LatestKnownOnlyPaysHistoricalDate : Set where
data ParserHandoffCreatesAtomicGate : Set where
data PNFObservationCreatesLegalApplicability : Set where
data CurrentTextMaySilentlyReplaceHistoricalText : Set where

localCorpusPathIsNotSemanticRequirement :
  LocalCorpusPathIsSemanticRequirement → ⊥
localCorpusPathIsNotSemanticRequirement ()

legalFollowDemandDoesNotCreateAuthority :
  LegalFollowDemandCreatesSourceAuthority → ⊥
legalFollowDemandDoesNotCreateAuthority ()

providerResolutionDoesNotCreateAuthority :
  ProviderResolutionCreatesLegalAuthority → ⊥
providerResolutionDoesNotCreateAuthority ()

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
    legalFollowDemandRequired : Bool
    governedResolutionReceiptRequired : Bool
    pinnedObservedRevisionRequired : Bool
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
    false true true true true true true false false false
