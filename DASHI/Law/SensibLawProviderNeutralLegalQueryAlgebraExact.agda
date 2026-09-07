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
  unorderedProximity
  leftBeforeRight
  rightBeforeLeft
  : ProximityDirection

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
  supportingProbe
  defeaterProbe
  comparatorProbe
  contradictionProbe
  counterexampleProbe
  vocabularyExplorationProbe
  authorityFamilyExplorationProbe
  : SearchProbeKind

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
  austliiProvider
  jadeProvider
  officialCourtProvider
  officialLegislationProvider
  wikipediaProvider
  wikidataProvider
  journalIndexProvider
  localWorldModelProvider
  : SearchProvider

data ProviderOperation : Set where
  textualSearchOperation
  exactCitationLookupOperation
  citedByTraversalOperation
  casesCitedTraversalOperation
  legislationCitedTraversalOperation
  entityLookupOperation
  corpusGraphLookupOperation
  : ProviderOperation

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
-- Concrete provider-neutral expressions.
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

orderedCommonLawDevelopmentQuery : QueryExpr
orderedCommonLawDevelopmentQuery = beforeQ 15
  (phraseQ "develop the common law")
  (phraseQ "duty of care")

------------------------------------------------------------------------
-- AustLII/SINO proximity is modelled explicitly rather than hidden inside a
-- string renderer. `near` is the provider's fixed broad proximity form;
-- `w/n` and `/n/` are unordered bounded forms; `pre/n` is ordered.
------------------------------------------------------------------------

data SinoProximityOperator : Set where
  sinoNear50
  sinoWithin : Nat → SinoProximityOperator
  sinoWithinAlias : Nat → SinoProximityOperator
  sinoPre : Nat → SinoProximityOperator

record AustLIIProximityLowering : Set where
  constructor austLIIProximityLowering
  field
    sourceConstraint : ProximityConstraint
    operator : SinoProximityOperator
    renderedSyntaxReference : String
    lexicalCandidateOnly : Bool
    lexicalCandidateOnlyIsTrue : lexicalCandidateOnly ≡ true
    loweringReference : String

open AustLIIProximityLowering public

dutyPolicyConstraint : ProximityConstraint
dutyPolicyConstraint = proximityConstraint
  (phraseQ "duty of care")
  (phraseQ "government policy")
  10
  unorderedProximity
  "duty-policy within ten indexed words"

maboQueenslandConstraint : ProximityConstraint
maboQueenslandConstraint = proximityConstraint
  (termQ "Mabo")
  (termQ "Queensland")
  2
  unorderedProximity
  "Mabo / Queensland within two indexed words"

orderedDevelopmentConstraint : ProximityConstraint
orderedDevelopmentConstraint = proximityConstraint
  (phraseQ "develop the common law")
  (phraseQ "duty of care")
  15
  leftBeforeRight
  "ordered common-law-development / duty relation candidate"

sinoNearFixture : AustLIIProximityLowering
sinoNearFixture = austLIIProximityLowering
  dutyPolicyConstraint
  sinoNear50
  "\"duty of care\" near \"government policy\""
  true refl
  "provider broad-near lowering; fixed provider window retained as provider semantics"

sinoWithinFixture : AustLIIProximityLowering
sinoWithinFixture = austLIIProximityLowering
  dutyPolicyConstraint
  (sinoWithin 10)
  "\"duty of care\" w/10 \"government policy\""
  true refl
  "provider-neutral unordered proximity lowered to SINO w/n"

sinoWithinAliasFixture : AustLIIProximityLowering
sinoWithinAliasFixture = austLIIProximityLowering
  dutyPolicyConstraint
  (sinoWithinAlias 10)
  "\"duty of care\" /10/ \"government policy\""
  true refl
  "same unordered proximity represented by the SINO /n/ alias"

sinoPreFixture : AustLIIProximityLowering
sinoPreFixture = austLIIProximityLowering
  orderedDevelopmentConstraint
  (sinoPre 15)
  "\"develop the common law\" pre/15 \"duty of care\""
  true refl
  "ordered proximity lowered to SINO pre/n"

------------------------------------------------------------------------
-- Finite executable-query compiler fixtures.
------------------------------------------------------------------------

data AustLIIQueryTemplate : Set where
  dutyPolicyTemplate
  maboQueenslandTemplate
  donoghueDevelopmentTemplate
  orderedCommonLawTemplate
  : AustLIIQueryTemplate

templateExpr : AustLIIQueryTemplate → QueryExpr
templateExpr dutyPolicyTemplate = dutyPolicyQuery
templateExpr maboQueenslandTemplate = maboQueenslandQuery
templateExpr donoghueDevelopmentTemplate = donoghueDevelopmentQuery
templateExpr orderedCommonLawTemplate = orderedCommonLawDevelopmentQuery

compileAustLII : AustLIIQueryTemplate → ProviderCompiledQuery
compileAustLII dutyPolicyTemplate = providerCompiledQuery
  dutyPolicyQuery
  austliiProvider
  textualSearchOperation
  "\"duty of care\" w/10 \"government policy\""
  ⊤
  "AustLII SINO proximity is lexical candidate generation only"
  "provider-neutral Near(10) lowered to AustLII w/10"
compileAustLII maboQueenslandTemplate = providerCompiledQuery
  maboQueenslandQuery
  austliiProvider
  textualSearchOperation
  "Mabo w/2 Queensland"
  ⊤
  "AustLII SINO proximity is lexical candidate generation only"
  "provider-neutral Near(2) lowered to AustLII w/2"
compileAustLII donoghueDevelopmentTemplate = providerCompiledQuery
  donoghueDevelopmentQuery
  austliiProvider
  textualSearchOperation
  "\"Donoghue v Stevenson\" w/20 (incremental or analogous or novel)"
  ⊤
  "runtime renderer must preserve Boolean grouping exactly"
  "known-authority doctrinal-development search fixture"
compileAustLII orderedCommonLawTemplate = providerCompiledQuery
  orderedCommonLawDevelopmentQuery
  austliiProvider
  textualSearchOperation
  "\"develop the common law\" pre/15 \"duty of care\""
  ⊤
  "ordered lexical proximity is candidate generation only"
  "provider-neutral Before(15) lowered to AustLII pre/15"

compiledAustLIIDutyPolicy : ProviderCompiledQuery
compiledAustLIIDutyPolicy = compileAustLII dutyPolicyTemplate

compiledAustLIIMaboQueensland : ProviderCompiledQuery
compiledAustLIIMaboQueensland = compileAustLII maboQueenslandTemplate

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

jadeLegislationCitedTraversal : String → CitationTraversal
jadeLegislationCitedTraversal authority = citationTraversal
  authority legislationCitedTraversalOperation jadeProvider 1
  "Jade legislation-cited graph traversal over an exact authority identity"

------------------------------------------------------------------------
-- Proximity and provider firewalls.
------------------------------------------------------------------------

data TextualProximityAutomaticallySemanticRelation : Set where
data ExecutableQueryStringDefinesSearchIntent : Set where
data ProviderSyntaxMayChangeProofObligation : Set where
data CitationTraversalAutomaticallyMeansFollowing : Set where
data QueryExpansionEqualsProofExpansion : Set where

data NearAndPreHaveSameDirectionSemantics : Set where

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

nearDoesNotCollapseIntoPre : NearAndPreHaveSameDirectionSemantics → ⊥
nearDoesNotCollapseIntoPre ()

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
    orderedAndUnorderedProximityRemainDistinct : Bool
    orderedAndUnorderedProximityRemainDistinctIsTrue :
      orderedAndUnorderedProximityRemainDistinct ≡ true

canonicalQueryAlgebraBoundary : QueryAlgebraBoundary
canonicalQueryAlgebraBoundary =
  queryAlgebraBoundary true refl false refl false refl true refl true refl
