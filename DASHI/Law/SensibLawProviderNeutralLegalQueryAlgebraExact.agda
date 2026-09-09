module DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent

------------------------------------------------------------------------
-- PROVIDER-NEUTRAL LEGAL QUERY ALGEBRA
--
-- Executable provider strings are lowerings of this object. They do not own
-- the research intent and lexical proximity is never upgraded to a semantic
-- relation merely because a backend returned a hit.
------------------------------------------------------------------------

data QueryExpr : Set where
  termQ : String → QueryExpr
  phraseQ : String → QueryExpr
  andQ : QueryExpr → QueryExpr → QueryExpr
  orQ : QueryExpr → QueryExpr → QueryExpr
  notQ : QueryExpr → QueryExpr
  nearQ : Nat → QueryExpr → QueryExpr → QueryExpr
  beforeQ : Nat → QueryExpr → QueryExpr → QueryExpr
  citationQ : String → QueryExpr
  courtQ : String → QueryExpr
  jurisdictionQ : String → QueryExpr
  dateRangeQ : String → String → QueryExpr
  treatmentQ : String → QueryExpr

data ProximityDirection : Set where
  unorderedProximity : ProximityDirection
  leftBeforeRight : ProximityDirection
  rightBeforeLeft : ProximityDirection


record ProximityConstraint : Set where
  constructor proximityConstraint
  field
    left : QueryExpr
    right : QueryExpr
    window : Nat
    direction : ProximityDirection
    constraintReference : String

open ProximityConstraint public

data SearchProbeKind : Set where
  supportingProbe : SearchProbeKind
  defeaterProbe : SearchProbeKind
  comparatorProbe : SearchProbeKind
  contradictionProbe : SearchProbeKind
  counterexampleProbe : SearchProbeKind
  vocabularyExplorationProbe : SearchProbeKind
  authorityFamilyExplorationProbe : SearchProbeKind


record SearchHypothesis : Set₁ where
  constructor searchHypothesis
  field
    intent : Intent.SearchIntent
    hypothesisReference : String
    expectedPropositionShape : String
    probeKind : SearchProbeKind
    query : QueryExpr
    proofGapPaymentReference : String
    exclusionReference : String

open SearchHypothesis public

record SearchHypothesisFamily : Set₁ where
  constructor searchHypothesisFamily
  field
    intent : Intent.SearchIntent
    primary : SearchHypothesis
    alternatives : List SearchHypothesis
    defeaters : List SearchHypothesis
    comparators : List SearchHypothesis
    familyReference : String

open SearchHypothesisFamily public

------------------------------------------------------------------------
-- Provider lowering boundary.
------------------------------------------------------------------------

data SearchProvider : Set where
  austliiProvider : SearchProvider
  jadeProvider : SearchProvider
  officialCourtProvider : SearchProvider
  officialLegislationProvider : SearchProvider
  wikipediaProvider : SearchProvider
  wikidataProvider : SearchProvider
  journalIndexProvider : SearchProvider
  localWorldModelProvider : SearchProvider


data ProviderOperation : Set where
  textualSearchOperation : ProviderOperation
  exactCitationLookupOperation : ProviderOperation
  citedByTraversalOperation : ProviderOperation
  casesCitedTraversalOperation : ProviderOperation
  legislationCitedTraversalOperation : ProviderOperation
  entityLookupOperation : ProviderOperation
  conceptNavigationOperation : ProviderOperation
  corpusGraphLookupOperation : ProviderOperation


record ProviderCompiledQuery : Set₁ where
  constructor providerCompiledQuery
  field
    sourceQuery : QueryExpr
    provider : SearchProvider
    operation : ProviderOperation
    renderedQuery : String
    semanticPreservationReceipt : Set
    providerLimitReference : String
    compilationReference : String

open ProviderCompiledQuery public

------------------------------------------------------------------------
-- Concrete AustLII / Jade fixtures.
--
-- The strings are provider representations of already-typed queries; no claim
-- is made that a lexical hit proves the semantic proposition.
------------------------------------------------------------------------

dutyPolicyQuery : QueryExpr
dutyPolicyQuery = nearQ 10 (phraseQ "duty of care") (phraseQ "government policy")

novelDutyQuery : QueryExpr
novelDutyQuery = andQ
  (phraseQ "duty of care")
  (orQ (termQ "novel") (orQ (termQ "incremental") (termQ "analogous")))

donoghueDevelopmentQuery : QueryExpr
donoghueDevelopmentQuery = nearQ 20
  (phraseQ "Donoghue v Stevenson")
  (orQ (termQ "incremental") (orQ (termQ "analogous") (termQ "novel")))

maboQueenslandQuery : QueryExpr
maboQueenslandQuery = nearQ 2 (termQ "Mabo") (termQ "Queensland")

compiledAustLIIDutyPolicy : ProviderCompiledQuery
compiledAustLIIDutyPolicy = providerCompiledQuery
  dutyPolicyQuery
  austliiProvider
  textualSearchOperation
  "\"duty of care\" w/10 \"government policy\""
  ⊤
  "AustLII SINO proximity is lexical candidate generation only"
  "provider-neutral Near(10) lowered to AustLII w/10"

compiledAustLIIMaboQueensland : ProviderCompiledQuery
compiledAustLIIMaboQueensland = providerCompiledQuery
  maboQueenslandQuery
  austliiProvider
  textualSearchOperation
  "Mabo w/2 Queensland"
  ⊤
  "AustLII SINO proximity is lexical candidate generation only"
  "provider-neutral Near(2) lowered to AustLII w/2"

record CitationTraversal : Set where
  constructor citationTraversal
  field
    authorityReference : String
    operation : ProviderOperation
    provider : SearchProvider
    traversalDepth : Nat
    traversalReference : String

open CitationTraversal public

jadeCitedByTraversal : String → CitationTraversal
jadeCitedByTraversal authority = citationTraversal
  authority citedByTraversalOperation jadeProvider 1
  "Jade cited-by graph traversal over an exact authority identity"

jadeCasesCitedTraversal : String → CitationTraversal
jadeCasesCitedTraversal authority = citationTraversal
  authority casesCitedTraversalOperation jadeProvider 1
  "Jade cases-cited graph traversal over an exact authority identity"

------------------------------------------------------------------------
-- Proximity and provider firewalls.
------------------------------------------------------------------------

data TextualProximityAutomaticallySemanticRelation : Set where
data ExecutableQueryStringDefinesSearchIntent : Set where
data ProviderSyntaxMayChangeProofObligation : Set where
data CitationTraversalAutomaticallyMeansFollowing : Set where
data QueryExpansionEqualsProofExpansion : Set where

proximityDoesNotProveSemanticRelation :
  TextualProximityAutomaticallySemanticRelation → ⊥
proximityDoesNotProveSemanticRelation ()

stringDoesNotDefineIntent : ExecutableQueryStringDefinesSearchIntent → ⊥
stringDoesNotDefineIntent ()

providerSyntaxDoesNotChangeProofObligation : ProviderSyntaxMayChangeProofObligation → ⊥
providerSyntaxDoesNotChangeProofObligation ()

citationTraversalDoesNotProveFollowing : CitationTraversalAutomaticallyMeansFollowing → ⊥
citationTraversalDoesNotProveFollowing ()

queryExpansionDoesNotEqualProofExpansion : QueryExpansionEqualsProofExpansion → ⊥
queryExpansionDoesNotEqualProofExpansion ()

record QueryAlgebraBoundary : Set where
  constructor queryAlgebraBoundary
  field
    proximityIsProviderNeutralBeforeLowering : Bool
    proximityIsProviderNeutralBeforeLoweringIsTrue :
      proximityIsProviderNeutralBeforeLowering ≡ true
    lexicalProximityEqualsSemanticRelation : Bool
    lexicalProximityEqualsSemanticRelationIsFalse :
      lexicalProximityEqualsSemanticRelation ≡ false
    providerStringOwnsResearchIntent : Bool
    providerStringOwnsResearchIntentIsFalse : providerStringOwnsResearchIntent ≡ false
    graphTraversalAndTextSearchRemainDistinct : Bool
    graphTraversalAndTextSearchRemainDistinctIsTrue :
      graphTraversalAndTextSearchRemainDistinct ≡ true

canonicalQueryAlgebraBoundary : QueryAlgebraBoundary
canonicalQueryAlgebraBoundary =
  queryAlgebraBoundary true refl false refl false refl true refl
