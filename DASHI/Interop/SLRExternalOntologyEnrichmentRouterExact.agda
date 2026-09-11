module DASHI.Interop.SLRExternalOntologyEnrichmentRouterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRWikimediaFirstWorldAcquisitionExact as Wikimedia

------------------------------------------------------------------------
-- EXTERNAL ONTOLOGY ENRICHMENT ROUTER
--
-- SensibLaw/ITIR source:
--   docs/external_ontologies.md
--   src/ontology/enrichment.py
--   scripts/dbpedia_lookup*.py
--
-- External providers remain advisory enrichment.  They may improve identity,
-- taxonomy, aliasing, clustering, or retrieval, but cannot manufacture legal
-- authority, claim truth, or canonical token/lexeme identity.
------------------------------------------------------------------------

data ExternalOntologyProvider : Set where
  wikidataProvider : ExternalOntologyProvider
  dbpediaProvider : ExternalOntologyProvider
  yagoProvider : ExternalOntologyProvider
  wordnetProvider : ExternalOntologyProvider
  schemaOrgProvider : ExternalOntologyProvider
  umbelProvider : ExternalOntologyProvider

record ExternalOntologyPolicy : Set where
  constructor externalOntologyPolicy
  field
    wikidataPrimaryIdentityGraph : Bool
    dbpediaAdvisoryFallback : Bool
    yagoTypedTaxonomyAdvisory : Bool
    wordnetVersionPinnedLexicalNormalizationOnly : Bool
    schemaOrgBroadCategoryAdvisory : Bool
    umbelBroadCategoryAdvisory : Bool
    reviewedExternalIdsRequiredForPromotion : Bool
    providerCandidateCreatesInternalOntologyTruth : Bool
    providerClassCreatesLegalNormativity : Bool
    lexicalSynonymCreatesEntityIdentity : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ExternalOntologyPolicy public

canonicalExternalOntologyPolicy : ExternalOntologyPolicy
canonicalExternalOntologyPolicy =
  externalOntologyPolicy
    true true true true true true true
    false false false true false

record ExternalOntologyResidualRoute : Set where
  constructor externalOntologyResidualRoute
  field
    consumerResidualReference : String
    wikimediaGraphTried : Bool
    dbpediaNeeded : Bool
    yagoNeeded : Bool
    wordnetNeeded : Bool
    broaderSnowballNeeded : Bool
    routingReasonReference : String

open ExternalOntologyResidualRoute public

canonicalResidualRouteBoundary : ExternalOntologyResidualRoute
canonicalResidualRouteBoundary =
  externalOntologyResidualRoute
    "consumer-specific world residual"
    true false false false false
    "additional providers are demand-driven after reviewed Wikimedia/world evidence"

wikimediaAcquisitionAnchor : Wikimedia.WikimediaFirstAcquisitionPolicy
wikimediaAcquisitionAnchor = Wikimedia.canonicalWikimediaFirstAcquisitionPolicy

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DBpediaCandidateIsInternalTruth : Set where
data YagoClassIsLegalCategory : Set where
data WordNetSynsetIsEntityIdentity : Set where
data ExternalOntologyMayOverrideCanonicalTokens : Set where

dbpediaCandidateDoesNotCreateTruth : DBpediaCandidateIsInternalTruth → ⊥
dbpediaCandidateDoesNotCreateTruth ()

yagoClassDoesNotCreateLegalCategory : YagoClassIsLegalCategory → ⊥
yagoClassDoesNotCreateLegalCategory ()

wordnetSynsetDoesNotCreateEntityIdentity : WordNetSynsetIsEntityIdentity → ⊥
wordnetSynsetDoesNotCreateEntityIdentity ()

externalOntologyDoesNotOverrideTokens : ExternalOntologyMayOverrideCanonicalTokens → ⊥
externalOntologyDoesNotOverrideTokens ()
