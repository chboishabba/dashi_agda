module DASHI.Interop.SLRWikidataRdfCandidateProviderExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRBinaryRouteCandidateParetoExact as Route
import DASHI.Interop.SLRResidualDrivenProducerPlannerExact as Producer

------------------------------------------------------------------------
-- WIKIDATA RDF/XML -> SLRG PROVIDER PARITY
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-wikimedia-candidate-provider
--
-- Provider reads Wikidata Special:EntityData/<QID>.rdf structurally and emits
-- only binary SLRG candidates. JSON/NDJSON and regex are not transport or
-- parsing surfaces in this provider.
------------------------------------------------------------------------

data DirectPropertyFamily : Set where
  P31 : DirectPropertyFamily
  P279 : DirectPropertyFamily
  P361 : DirectPropertyFamily
  P527 : DirectPropertyFamily
  P131 : DirectPropertyFamily
  P17 : DirectPropertyFamily
  P1269 : DirectPropertyFamily

propertySpecificity : DirectPropertyFamily → Nat
propertySpecificity P31 = 5
propertySpecificity P279 = 5
propertySpecificity P361 = 4
propertySpecificity P527 = 4
propertySpecificity P131 = 3
propertySpecificity P17 = 3
propertySpecificity P1269 = 3

propertyProducer : DirectPropertyFamily → Producer.ProducerFamily
propertyProducer P31 = Producer.classificationEvidence
propertyProducer P279 = Producer.classificationEvidence
propertyProducer P361 = Producer.identitySource
propertyProducer P527 = Producer.identitySource
propertyProducer P131 = Producer.identitySource
propertyProducer P17 = Producer.identitySource
propertyProducer P1269 = Producer.identitySource

wikidataRouteFamilyTag : Nat
wikidataRouteFamilyTag = Route.routeFamilyTag Route.wikidataProperty

wikipediaArticleRouteFamilyTag : Nat
wikipediaArticleRouteFamilyTag = Route.routeFamilyTag Route.wikipediaArticle

record WikidataRdfCandidateProviderParity : Set where
  constructor wikidataRdfCandidateProviderParity
  field
    sourceRepresentationIsRdfXml : Bool
    specialEntityDataRdfUsed : Bool
    jsonEndpointUsed : Bool
    regexParserUsed : Bool
    qidSyntaxCheckedStructurally : Bool
    reviewedDirectPropertiesOnly : Bool
    p31P279UseClassificationProducer : Bool
    relationPropertiesUseIdentityProducer : Bool
    enwikiSitelinkProducesArticleSemanticCandidate : Bool
    producerSearchCandidatesRequireVerifiedRootQID : Bool
    searchCandidateAlreadyIsEvidence : Bool
    routeCandidateCreatesClaimTruth : Bool
    routeCandidateCreatesSemanticAuthority : Bool
    qidIdentityIsOntologyTransplant : Bool
    typedPropertyCreatesClaimTruth : Bool
    emittedFormatIsSLRG : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open WikidataRdfCandidateProviderParity public

canonicalWikidataRdfCandidateProviderParity : WikidataRdfCandidateProviderParity
canonicalWikidataRdfCandidateProviderParity =
  wikidataRdfCandidateProviderParity
    true true false false true true true true true true
    false false false false false true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data JsonWikidataProviderTransport : Set where
data RegexWikidataProviderParser : Set where
data SearchCandidateAlreadyIsEvidence : Set where
data RdfCandidateCreatesClaimTruth : Set where
data RdfCandidateCreatesSemanticAuthority : Set where
data QidIdentityCreatesOntologyTransplant : Set where
data TypedPropertyCreatesClaimTruth : Set where

jsonWikidataProviderTransportForbidden : JsonWikidataProviderTransport → ⊥
jsonWikidataProviderTransportForbidden ()

regexWikidataProviderParserForbidden : RegexWikidataProviderParser → ⊥
regexWikidataProviderParserForbidden ()

searchCandidateDoesNotCreateEvidence : SearchCandidateAlreadyIsEvidence → ⊥
searchCandidateDoesNotCreateEvidence ()

rdfCandidateDoesNotCreateClaimTruth : RdfCandidateCreatesClaimTruth → ⊥
rdfCandidateDoesNotCreateClaimTruth ()

rdfCandidateDoesNotCreateSemanticAuthority : RdfCandidateCreatesSemanticAuthority → ⊥
rdfCandidateDoesNotCreateSemanticAuthority ()

qidIdentityDoesNotTransplantOntology : QidIdentityCreatesOntologyTransplant → ⊥
qidIdentityDoesNotTransplantOntology ()

typedPropertyDoesNotCreateClaimTruth : TypedPropertyCreatesClaimTruth → ⊥
typedPropertyDoesNotCreateClaimTruth ()

routeCandidateWireVersionAnchor : Nat
routeCandidateWireVersionAnchor = Route.routeCandidateWireVersion
