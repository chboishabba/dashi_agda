module DASHI.Interop.SLRSelectedRouteExecutionNextObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRBinaryRouteCandidateParetoExact as Route
import DASHI.Interop.SLRResidualDrivenProducerPlannerExact as Producer
import DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact as Observation

------------------------------------------------------------------------
-- SELECTED ROUTE EXECUTION -> ACQUIRED SOURCE -> NEXT SLRO
--
-- Runtime owners:
--   chboishabba/slr :: crates/sl-route-executor
--   dashi_agda :: tools/slr-discourse-reconstruct/slr_spacy_observation_wire.py
--
-- Executable first slice:
--   RTA2(ArticleSemantic, WikipediaArticle)
--     -> HTTPS *.wikipedia.org rendered article
--     -> SLRX v1 acquired-source frame
--     -> trained spaCy boundary
--     -> SLRO v1 next observation stream.
--
-- Search-family and parser-repair RTA2 routes are deliberately deferred. They
-- do not become synthetic source text merely because they were selected.
------------------------------------------------------------------------

acquiredSourceWireVersion : Nat
acquiredSourceWireVersion = 1

wikipediaRenderedHtmlSourceTag : Nat
wikipediaRenderedHtmlSourceTag = 1

articleSemanticProducerTag : Nat
articleSemanticProducerTag = Producer.producerFamilyTag Producer.articleSemantic

wikipediaArticleRouteTag : Nat
wikipediaArticleRouteTag = Route.routeFamilyTag Route.wikipediaArticle

record AcquiredSourceBodyParity : Set where
  constructor acquiredSourceBodyParity
  field
    magicIsSLRX : Bool
    versionIsOne : Bool
    wikipediaRenderedHtmlTagIsOne : Bool
    candidateOnlyFlagSet : Bool
    semanticPromotionFlagClear : Bool
    documentReferenceRetained : Bool
    sourceQIDReferenceRetained : Bool
    languageRetained : Bool
    revisionReferenceRetained : Bool
    canonicalURLRetained : Bool
    sourceSHA256Retained : Bool
    renderedUTF8TextRetained : Bool

open AcquiredSourceBodyParity public

canonicalAcquiredSourceBodyParity : AcquiredSourceBodyParity
canonicalAcquiredSourceBodyParity =
  acquiredSourceBodyParity
    true true true true true true true true true true true true

record SelectedRouteExecutionParity : Set where
  constructor selectedRouteExecutionParity
  field
    inputBodyMagicIsRTA2 : Bool
    articleSemanticProducerRequired : Bool
    wikipediaArticleRouteRequired : Bool
    selectedRouteMustRemainCandidateOnly : Bool
    selectedRouteMustRemainNonPromoting : Bool
    targetMustUseHTTPS : Bool
    targetMustBeWikipediaHost : Bool
    arbitrarySelectedURLMayBeFetched : Bool
    renderedMarkupParsedStructurallyInRust : Bool
    acquisitionUsesJson : Bool
    acquisitionUsesRegexSemanticParser : Bool
    missingETagFallsBackToContentDigestIdentity : Bool
    unsupportedSearchRouteCreatesSyntheticSource : Bool
    unsupportedRouteIsDeferred : Bool
    acquisitionCreatesClaimTruth : Bool
    acquisitionCreatesEvidencePayment : Bool
    acquiredSourceCreatesSemanticAuthority : Bool

open SelectedRouteExecutionParity public

canonicalSelectedRouteExecutionParity : SelectedRouteExecutionParity
canonicalSelectedRouteExecutionParity =
  selectedRouteExecutionParity
    true true true true true true true false true false false true
    false true false false false

record AcquiredSourceToObservationParity : Set where
  constructor acquiredSourceToObservationParity
  field
    pythonBoundaryOnlyDecodesSLRXAndRunsSpacy : Bool
    acquiredDigestVerifiedBeforeParsing : Bool
    acquiredManifestationsRemainSeparate : Bool
    nextObservationMagicIsSLRO : Bool
    nextObservationUsesExistingDependencyShapeMap : Bool
    nextObservationRetainsDocumentReference : Bool
    nextObservationRetainsSourceQID : Bool
    nextObservationRetainsLanguage : Bool
    nextObservationRetainsRevisionReference : Bool
    pythonPerformsAcquisition : Bool
    pythonPerformsMarkupSemanticParsing : Bool
    pythonPerformsWorldSemantics : Bool
    jsonTransportUsed : Bool
    regexSemanticParserUsed : Bool
    nextObservationCreatesClaimTruth : Bool
    nextObservationPromotesSemantics : Bool

open AcquiredSourceToObservationParity public

canonicalAcquiredSourceToObservationParity : AcquiredSourceToObservationParity
canonicalAcquiredSourceToObservationParity =
  acquiredSourceToObservationParity
    true true true true true true true true true
    false false false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ArbitrarySelectedURLFetch : Set where
data UnsupportedRouteCreatesSyntheticSource : Set where
data AcquisitionCreatesClaimTruth : Set where
data AcquisitionCreatesEvidencePayment : Set where
data AcquisitionCreatesSemanticAuthority : Set where
data PythonPerformsAcquisition : Set where
data PythonPerformsWorldSemantics : Set where
data AcquiredSourceJsonTransport : Set where
data AcquiredSourceRegexSemanticParser : Set where

arbitrarySelectedURLFetchForbidden : ArbitrarySelectedURLFetch → ⊥
arbitrarySelectedURLFetchForbidden ()

unsupportedRouteCannotCreateSyntheticSource : UnsupportedRouteCreatesSyntheticSource → ⊥
unsupportedRouteCannotCreateSyntheticSource ()

acquisitionDoesNotCreateClaimTruth : AcquisitionCreatesClaimTruth → ⊥
acquisitionDoesNotCreateClaimTruth ()

acquisitionDoesNotPayEvidenceByItself : AcquisitionCreatesEvidencePayment → ⊥
acquisitionDoesNotPayEvidenceByItself ()

acquisitionDoesNotCreateSemanticAuthority : AcquisitionCreatesSemanticAuthority → ⊥
acquisitionDoesNotCreateSemanticAuthority ()

pythonAcquisitionForbidden : PythonPerformsAcquisition → ⊥
pythonAcquisitionForbidden ()

pythonWorldSemanticsForbidden : PythonPerformsWorldSemantics → ⊥
pythonWorldSemanticsForbidden ()

acquiredSourceJsonTransportForbidden : AcquiredSourceJsonTransport → ⊥
acquiredSourceJsonTransportForbidden ()

acquiredSourceRegexSemanticParserForbidden : AcquiredSourceRegexSemanticParser → ⊥
acquiredSourceRegexSemanticParserForbidden ()

nextObservationWireVersionAnchor : Nat
nextObservationWireVersionAnchor = Observation.observationWireVersion
