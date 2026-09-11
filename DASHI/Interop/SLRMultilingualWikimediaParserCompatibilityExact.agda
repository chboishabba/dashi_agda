module DASHI.Interop.SLRMultilingualWikimediaParserCompatibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRWikimediaFirstWorldAcquisitionExact as Wikimedia

------------------------------------------------------------------------
-- MULTILINGUAL WIKIMEDIA / PARSER COMPATIBILITY
--
-- SensibLaw anchors:
--   src/sources/translation_view.py
--   src/sources/normalized_source.py
--   src/text/nlp.py
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_multilingual_wikimedia_parser_compat.py
--   tools/slr-discourse-reconstruct/run_multilingual_wikimedia_parser_compat.sh
--
-- A Wikidata QID can anchor identity across language-specific Wikipedia
-- sitelinks.  This does not make the language surfaces translations of one
-- another, and parser-shape compatibility does not establish semantic parity.
------------------------------------------------------------------------

record MultilingualIdentityBoundary : Set where
  constructor multilingualIdentityBoundary
  field
    sharedQidPaysCrossLanguageEntityIdentity : Bool
    sharedQidPaysTranslationEquivalence : Bool
    sameWikipediaTopicPaysSentenceAlignment : Bool
    parserSchemaCompatibilityPaysSemanticEquivalence : Bool
    trainedParserAndBlankFallbackAreSameEvidenceClass : Bool
    languageSurfaceProvenanceRetained : Bool
    translationDriftMayRemainResidual : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open MultilingualIdentityBoundary public

canonicalMultilingualIdentityBoundary : MultilingualIdentityBoundary
canonicalMultilingualIdentityBoundary =
  multilingualIdentityBoundary true false false false false true true true false

record LanguageSurfaceReceipt : Set where
  constructor languageSurfaceReceipt
  field
    qidReference : String
    languageReference : String
    wikipediaTitleReference : String
    textDigestReference : String
    parserBackendReference : String
    parserModelReference : String
    trainedModelLoaded : Bool
    dependencyCapable : Bool
    sameQidIdentityPaid : Bool
    translationEquivalencePaid : Bool
    claimSemanticEquivalencePaid : Bool

open LanguageSurfaceReceipt public

exampleLanguageSurfaceBoundary : LanguageSurfaceReceipt
exampleLanguageSurfaceBoundary =
  languageSurfaceReceipt
    "QID supplied by reviewed Wikimedia graph"
    "ISO language code"
    "language-edition sitelink"
    "SHA-256 of fetched intro surface"
    "spaCy trained / spaCy blank / unavailable"
    "versioned runtime model reference"
    false false true false false

record SensibLawTranslationCompatibility : Set where
  constructor sensibLawTranslationCompatibility
  field
    translationViewSourceIdCompatible : Bool
    targetLanguageCompatible : Bool
    translatorProvenanceCompatible : Bool
    driftFlagCompatible : Bool
    normalizedSourceLanguageCompatible : Bool
    normalizedSourceTranslationStatusCompatible : Bool
    spacyLanguageAdapterCompatible : Bool
    universalDependenciesFallbackCompatible : Bool

open SensibLawTranslationCompatibility public

canonicalSensibLawTranslationCompatibility : SensibLawTranslationCompatibility
canonicalSensibLawTranslationCompatibility =
  sensibLawTranslationCompatibility true true true true true true true true

wikimediaAcquisitionAnchor : Wikimedia.WikimediaFirstAcquisitionPolicy
wikimediaAcquisitionAnchor = Wikimedia.canonicalWikimediaFirstAcquisitionPolicy

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SharedQidMeansTranslationEquivalence : Set where
data SameTopicMeansSentenceAlignment : Set where
data ParserCompatibilityMeansSemanticEquivalence : Set where
data BlankParserEqualsTrainedDependencyParser : Set where

sharedQidDoesNotCreateTranslationEquivalence : SharedQidMeansTranslationEquivalence → ⊥
sharedQidDoesNotCreateTranslationEquivalence ()

sameTopicDoesNotCreateSentenceAlignment : SameTopicMeansSentenceAlignment → ⊥
sameTopicDoesNotCreateSentenceAlignment ()

parserCompatibilityDoesNotCreateSemanticEquivalence : ParserCompatibilityMeansSemanticEquivalence → ⊥
parserCompatibilityDoesNotCreateSemanticEquivalence ()

blankParserDoesNotEqualTrainedDependencyParser : BlankParserEqualsTrainedDependencyParser → ⊥
blankParserDoesNotEqualTrainedDependencyParser ()

-- Backward-compatible spelling retained for any shallow consumers already
-- importing the shorter name.
blankParserDoesNotEqualTrainedParser : BlankParserEqualsTrainedDependencyParser → ⊥
blankParserDoesNotEqualTrainedParser = blankParserDoesNotEqualTrainedDependencyParser
