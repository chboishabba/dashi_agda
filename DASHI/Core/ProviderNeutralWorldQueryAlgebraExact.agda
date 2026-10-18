module DASHI.Core.ProviderNeutralWorldQueryAlgebraExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- PROVIDER-NEUTRAL WORLD QUERY ALGEBRA
--
-- Generalises only the non-legal part of SensibLaw's provider-neutral search
-- architecture.  A typed residual owns the research intent; provider syntax is
-- a lowering target.  A returned hit remains a candidate artifact until it
-- re-enters the relevant parser/PNF/assessment pipeline.
------------------------------------------------------------------------

data WorldQueryExpr : Set where
  termQ : String → WorldQueryExpr
  phraseQ : String → WorldQueryExpr
  andQ : WorldQueryExpr → WorldQueryExpr → WorldQueryExpr
  orQ : WorldQueryExpr → WorldQueryExpr → WorldQueryExpr
  notQ : WorldQueryExpr → WorldQueryExpr
  nearQ : Nat → WorldQueryExpr → WorldQueryExpr → WorldQueryExpr

  entityQ : String → WorldQueryExpr
  relationQ : String → WorldQueryExpr
  propertyQ : String → WorldQueryExpr
  locationQ : String → WorldQueryExpr
  dateRangeQ : String → String → WorldQueryExpr
  sourceTypeQ : String → WorldQueryExpr
  siteQ : String → WorldQueryExpr
  identifierQ : String → WorldQueryExpr

data WorldProbeKind : Set where
  supportingProbe
  defeaterProbe
  comparatorProbe
  contradictionProbe
  counterexampleProbe
  vocabularyExplorationProbe
  authorityFamilyExplorationProbe :
    WorldProbeKind

record WorldSearchHypothesis : Set where
  constructor world-search-hypothesis
  field
    consumerReference : String
    residualReference : String
    hypothesisReference : String
    expectedPropositionShape : String
    probeKind : WorldProbeKind
    query : WorldQueryExpr
    exclusionReference : String
    paymentConditionReference : String

open WorldSearchHypothesis public

record WorldSearchHypothesisFamily : Set where
  constructor world-search-hypothesis-family
  field
    primary : WorldSearchHypothesis
    alternatives : List WorldSearchHypothesis
    defeaters : List WorldSearchHypothesis
    comparators : List WorldSearchHypothesis
    contradictions : List WorldSearchHypothesis
    familyReference : String

open WorldSearchHypothesisFamily public

data WorldSearchProvider : Set where
  localWorldProvider
  wikidataProvider
  wikipediaProvider
  officialSourceProvider
  webSearchProvider
  scholarlyIndexProvider
  citationGraphProvider :
    WorldSearchProvider

data WorldProviderOperation : Set where
  textualSearchOperation
  entityLookupOperation
  propertyTraversalOperation
  relatedEntityTraversalOperation
  sourceInspectionOperation
  citationTraversalOperation :
    WorldProviderOperation

record WorldProviderCompiledQuery : Set where
  constructor world-provider-compiled-query
  field
    sourceQuery : WorldQueryExpr
    provider : WorldSearchProvider
    operation : WorldProviderOperation
    renderedQuery : String
    semanticPreservationReference : String
    providerLimitReference : String
    compilationReference : String

open WorldProviderCompiledQuery public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ProviderStringDefinesResearchIntent : Set where
data SearchHitAutomaticallyPaysResidual : Set where
data LexicalProximityCreatesSemanticRelation : Set where
data ExternalOntologyEdgeCreatesInternalTruth : Set where
data QueryExpansionEqualsEvidenceExpansion : Set where

providerStringDoesNotDefineIntent :
  ProviderStringDefinesResearchIntent → ⊥
providerStringDoesNotDefineIntent ()

searchHitDoesNotPayResidual :
  SearchHitAutomaticallyPaysResidual → ⊥
searchHitDoesNotPayResidual ()

proximityDoesNotCreateRelation :
  LexicalProximityCreatesSemanticRelation → ⊥
proximityDoesNotCreateRelation ()

externalEdgeDoesNotCreateInternalTruth :
  ExternalOntologyEdgeCreatesInternalTruth → ⊥
externalEdgeDoesNotCreateInternalTruth ()

queryExpansionDoesNotEqualEvidenceExpansion :
  QueryExpansionEqualsEvidenceExpansion → ⊥
queryExpansionDoesNotEqualEvidenceExpansion ()

record ProviderNeutralWorldQueryBoundary : Set where
  constructor provider-neutral-world-query-boundary
  field
    typedResidualPrecedesProvider : Bool
    typedResidualPrecedesProviderIsTrue :
      typedResidualPrecedesProvider ≡ true

    providerStringOwnsIntent : Bool
    providerStringOwnsIntentIsFalse :
      providerStringOwnsIntent ≡ false

    searchHitEqualsPayment : Bool
    searchHitEqualsPaymentIsFalse :
      searchHitEqualsPayment ≡ false

    wikidataNavigationCreatesCanonicalOntology : Bool
    wikidataNavigationCreatesCanonicalOntologyIsFalse :
      wikidataNavigationCreatesCanonicalOntology ≡ false

    supportAndDefeaterCanShareOneTypedFamily : Bool
    supportAndDefeaterCanShareOneTypedFamilyIsTrue :
      supportAndDefeaterCanShareOneTypedFamily ≡ true

canonicalProviderNeutralWorldQueryBoundary :
  ProviderNeutralWorldQueryBoundary
canonicalProviderNeutralWorldQueryBoundary =
  provider-neutral-world-query-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
