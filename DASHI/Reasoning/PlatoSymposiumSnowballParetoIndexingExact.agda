module DASHI.Reasoning.PlatoSymposiumSnowballParetoIndexingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.RecursiveParetoFrontierLiftingExact as Pareto
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal
import DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeExact as Plato
import DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact as Source
import DASHI.Reasoning.PlatoSymposiumTransmissionAttributionExact as Transmission

------------------------------------------------------------------------
-- PLATO SYMPOSIUM SNOWBALL / PARETO / DEWEY / QID INDEXING BRIDGE
--
-- This is a thin governance owner over existing repository machinery.
-- It does not create a new citation ontology, traversal graph, Pareto planner,
-- or source-authority calculus.
--
-- Existing authority owners:
--   * SnowballAttributionProvenanceInvariantExact keeps author/title/source
--     kind/formalisation relationship/visibility/proof/authority coordinates;
--   * DashiKnowledgeTraversalFunnelExact treats Dewey/QID/source IDs as
--     traversal coordinates, not proof or semantic authority;
--   * RecursiveParetoFrontierLiftingExact allows residual-relevant frontier
--     refinement but explicitly denies proof authority from Pareto position;
--   * PlatoSymposiumTransmissionAttributionExact owns the layered dramatic /
--     reported-source / author / formalisation transmission distinction.
--
-- The new results below show that indexing, citation count and Pareto position
-- are insufficient projections for the consumers we actually care about.
------------------------------------------------------------------------

existingAttributionSnowballBoundary : Snowball.AttributionSnowballBoundary
existingAttributionSnowballBoundary = Snowball.canonicalAttributionSnowballBoundary

existingKnowledgeTraversalBoundary : Traversal.DashiKnowledgeTraversalBoundary
existingKnowledgeTraversalBoundary = Traversal.canonicalDashiKnowledgeTraversalBoundary

existingRecursiveParetoBoundary : Pareto.RecursiveParetoFrontierBoundary
existingRecursiveParetoBoundary = Pareto.canonicalRecursiveParetoFrontierBoundary

existingTransmissionBoundary : Transmission.PlatoSymposiumTransmissionBoundary
existingTransmissionBoundary = Transmission.canonicalPlatoSymposiumTransmissionBoundary

jmdBundleSourcePinned = Source.jmdBundleSource
rightOpinionSourceContract : Plato.LeanPhilosophyTheoremContract
rightOpinionSourceContract = Plato.rightOpinionContract

------------------------------------------------------------------------
-- Source-role discipline.
------------------------------------------------------------------------

data SourceRole : Set where
  primaryHistoricalText : SourceRole
  criticalEditionOrTranslation : SourceRole
  scholarlySecondarySource : SourceRole
  jmdFormalisationSource : SourceRole
  dashiStructuralBridge : SourceRole
  externalIndexCoordinate : SourceRole

data SourceAuthority : Set where
  historicalTextAuthority : SourceAuthority
  editorialCarrierAuthority : SourceAuthority
  interpretiveSecondaryAuthority : SourceAuthority
  formalisationAuthorityOnly : SourceAuthority
  bridgeAuthorityOnly : SourceAuthority
  traversalOnlyNoSourceAuthority : SourceAuthority

sourceAuthorityOf : SourceRole → SourceAuthority
sourceAuthorityOf primaryHistoricalText = historicalTextAuthority
sourceAuthorityOf criticalEditionOrTranslation = editorialCarrierAuthority
sourceAuthorityOf scholarlySecondarySource = interpretiveSecondaryAuthority
sourceAuthorityOf jmdFormalisationSource = formalisationAuthorityOnly
sourceAuthorityOf dashiStructuralBridge = bridgeAuthorityOnly
sourceAuthorityOf externalIndexCoordinate = traversalOnlyNoSourceAuthority

------------------------------------------------------------------------
-- 1. QID does not determine source authority.
------------------------------------------------------------------------

data QIDWorld : Set where
  qidAttachedToPrimaryText : QIDWorld
  qidAttachedToFormalisation : QIDWorld

data QIDSurface : Set where
  sameConceptQID : QIDSurface

data QIDAuthorityQuery : Set where
  sourceAuthorityQuestionByQID : QIDAuthorityQuery

data AuthorityAnswer : Set where
  primaryTextAnswer : AuthorityAnswer
  formalisationOnlyAnswer : AuthorityAnswer

qidProjection : QIDWorld → QIDSurface
qidProjection qidAttachedToPrimaryText = sameConceptQID
qidProjection qidAttachedToFormalisation = sameConceptQID

QIDAuthorityAnswerFor : QIDAuthorityQuery → Set
QIDAuthorityAnswerFor sourceAuthorityQuestionByQID = AuthorityAnswer

askQIDAuthority :
  (query : QIDAuthorityQuery) → QIDWorld → QIDAuthorityAnswerFor query
askQIDAuthority sourceAuthorityQuestionByQID qidAttachedToPrimaryText = primaryTextAnswer
askQIDAuthority sourceAuthorityQuestionByQID qidAttachedToFormalisation = formalisationOnlyAnswer

qidAuthorityQuestions : Query.InquiryQuestionFamily QIDWorld QIDAuthorityQuery
qidAuthorityQuestions = Query.inquiryQuestionFamily QIDAuthorityAnswerFor askQIDAuthority

qidDoesNotDetermineSourceAuthority :
  Query.FactorsThrough qidAuthorityQuestions qidProjection sourceAuthorityQuestionByQID → ⊥
qidDoesNotDetermineSourceAuthority factor = helper first second
  where
    first : primaryTextAnswer ≡ Query.quotientAnswer factor sameConceptQID
    first = Query.factorisation factor qidAttachedToPrimaryText

    second : formalisationOnlyAnswer ≡ Query.quotientAnswer factor sameConceptQID
    second = Query.factorisation factor qidAttachedToFormalisation

    helper :
      primaryTextAnswer ≡ Query.quotientAnswer factor sameConceptQID →
      formalisationOnlyAnswer ≡ Query.quotientAnswer factor sameConceptQID → ⊥
    helper refl ()

------------------------------------------------------------------------
-- 2. Dewey class does not determine source authority.
------------------------------------------------------------------------

data DeweyWorld : Set where
  philosophyPrimaryCarrier : DeweyWorld
  philosophySecondaryCommentary : DeweyWorld

data DeweySurface : Set where
  samePhilosophyClass : DeweySurface

data DeweyAuthorityQuery : Set where
  sourceAuthorityQuestionByDewey : DeweyAuthorityQuery

DeweyAuthorityAnswerFor : DeweyAuthorityQuery → Set
DeweyAuthorityAnswerFor sourceAuthorityQuestionByDewey = AuthorityAnswer

askDeweyAuthority :
  (query : DeweyAuthorityQuery) → DeweyWorld → DeweyAuthorityAnswerFor query
askDeweyAuthority sourceAuthorityQuestionByDewey philosophyPrimaryCarrier = primaryTextAnswer
askDeweyAuthority sourceAuthorityQuestionByDewey philosophySecondaryCommentary = formalisationOnlyAnswer

deweyProjection : DeweyWorld → DeweySurface
deweyProjection philosophyPrimaryCarrier = samePhilosophyClass
deweyProjection philosophySecondaryCommentary = samePhilosophyClass

deweyAuthorityQuestions : Query.InquiryQuestionFamily DeweyWorld DeweyAuthorityQuery
deweyAuthorityQuestions = Query.inquiryQuestionFamily DeweyAuthorityAnswerFor askDeweyAuthority

deweyDoesNotDetermineSourceAuthority :
  Query.FactorsThrough deweyAuthorityQuestions deweyProjection sourceAuthorityQuestionByDewey → ⊥
deweyDoesNotDetermineSourceAuthority factor = helper first second
  where
    first : primaryTextAnswer ≡ Query.quotientAnswer factor samePhilosophyClass
    first = Query.factorisation factor philosophyPrimaryCarrier

    second : formalisationOnlyAnswer ≡ Query.quotientAnswer factor samePhilosophyClass
    second = Query.factorisation factor philosophySecondaryCommentary

    helper :
      primaryTextAnswer ≡ Query.quotientAnswer factor samePhilosophyClass →
      formalisationOnlyAnswer ≡ Query.quotientAnswer factor samePhilosophyClass → ⊥
    helper refl ()

------------------------------------------------------------------------
-- 3. Citation count does not determine independent support.
------------------------------------------------------------------------

data CitationWorld : Set where
  repeatedDependentCitations : CitationWorld
  genuinelyIndependentSources : CitationWorld

data CitationCountSurface : Set where
  sameCitationCount : CitationCountSurface

data IndependenceQuery : Set where
  independentSupportQuestion : IndependenceQuery

data IndependenceAnswer : Set where
  dependentRepetition : IndependenceAnswer
  independentSupport : IndependenceAnswer

citationCountProjection : CitationWorld → CitationCountSurface
citationCountProjection repeatedDependentCitations = sameCitationCount
citationCountProjection genuinelyIndependentSources = sameCitationCount

IndependenceAnswerFor : IndependenceQuery → Set
IndependenceAnswerFor independentSupportQuestion = IndependenceAnswer

askIndependentSupport :
  (query : IndependenceQuery) → CitationWorld → IndependenceAnswerFor query
askIndependentSupport independentSupportQuestion repeatedDependentCitations = dependentRepetition
askIndependentSupport independentSupportQuestion genuinelyIndependentSources = independentSupport

independenceQuestions : Query.InquiryQuestionFamily CitationWorld IndependenceQuery
independenceQuestions = Query.inquiryQuestionFamily IndependenceAnswerFor askIndependentSupport

citationCountDoesNotDetermineIndependentSupport :
  Query.FactorsThrough independenceQuestions citationCountProjection independentSupportQuestion → ⊥
citationCountDoesNotDetermineIndependentSupport factor = helper first second
  where
    first : dependentRepetition ≡ Query.quotientAnswer factor sameCitationCount
    first = Query.factorisation factor repeatedDependentCitations

    second : independentSupport ≡ Query.quotientAnswer factor sameCitationCount
    second = Query.factorisation factor genuinelyIndependentSources

    helper :
      dependentRepetition ≡ Query.quotientAnswer factor sameCitationCount →
      independentSupport ≡ Query.quotientAnswer factor sameCitationCount → ⊥
    helper refl ()

------------------------------------------------------------------------
-- 4. Pareto rank does not determine consumer adequacy.
------------------------------------------------------------------------

data ParetoWorld : Set where
  sameRankPaidForConsumer : ParetoWorld
  sameRankUnpaidForConsumer : ParetoWorld

data ParetoRankSurface : Set where
  sameFrontierRank : ParetoRankSurface

data ConsumerAdequacyQuery : Set where
  consumerAdequacyQuestion : ConsumerAdequacyQuery

data ConsumerAdequacyAnswer : Set where
  consumerAdequate : ConsumerAdequacyAnswer
  consumerStillUnpaid : ConsumerAdequacyAnswer

paretoRankProjection : ParetoWorld → ParetoRankSurface
paretoRankProjection sameRankPaidForConsumer = sameFrontierRank
paretoRankProjection sameRankUnpaidForConsumer = sameFrontierRank

ConsumerAdequacyAnswerFor : ConsumerAdequacyQuery → Set
ConsumerAdequacyAnswerFor consumerAdequacyQuestion = ConsumerAdequacyAnswer

askConsumerAdequacy :
  (query : ConsumerAdequacyQuery) → ParetoWorld → ConsumerAdequacyAnswerFor query
askConsumerAdequacy consumerAdequacyQuestion sameRankPaidForConsumer = consumerAdequate
askConsumerAdequacy consumerAdequacyQuestion sameRankUnpaidForConsumer = consumerStillUnpaid

consumerAdequacyQuestions : Query.InquiryQuestionFamily ParetoWorld ConsumerAdequacyQuery
consumerAdequacyQuestions = Query.inquiryQuestionFamily ConsumerAdequacyAnswerFor askConsumerAdequacy

paretoRankDoesNotDetermineConsumerAdequacy :
  Query.FactorsThrough consumerAdequacyQuestions paretoRankProjection consumerAdequacyQuestion → ⊥
paretoRankDoesNotDetermineConsumerAdequacy factor = helper first second
  where
    first : consumerAdequate ≡ Query.quotientAnswer factor sameFrontierRank
    first = Query.factorisation factor sameRankPaidForConsumer

    second : consumerStillUnpaid ≡ Query.quotientAnswer factor sameFrontierRank
    second = Query.factorisation factor sameRankUnpaidForConsumer

    helper :
      consumerAdequate ≡ Query.quotientAnswer factor sameFrontierRank →
      consumerStillUnpaid ≡ Query.quotientAnswer factor sameFrontierRank → ⊥
    helper refl ()

------------------------------------------------------------------------
-- Explicit indexing coordinates for the Plato lane.
-- These are traversal hints only.  Empty/unresolved QIDs remain legitimate;
-- no identifier is invented here.
------------------------------------------------------------------------

platoPhilosophyCoordinate : Traversal.DashiKnowledgeCoordinate
platoPhilosophyCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Philosophy/PlatoSymposiumPhilosophyBridgeExact.agda"
  "Plato Symposium philosophy bridge"
  "100 philosophy / 180 ancient, medieval and eastern philosophy"
  ""
  "JMD attached Aristotle Symposium bundle; primary/critical-text acquisition remains separate"

platoHyperformalCoordinate : Traversal.DashiKnowledgeCoordinate
platoHyperformalCoordinate = Traversal.dashi-knowledge-coordinate
  "DASHI/Reasoning/PlatoSymposiumDialecticBraidHyperformalExact.agda"
  "Plato Symposium dialectic/braid/hyperfabric structural bridge"
  "100 philosophy + 510 mathematics/combinatorics traversal only"
  ""
  "JMD attached source contract plus DASHI-owned structural comparison"

platoIndexEdge : Traversal.DashiFirstLinkEdge
platoIndexEdge = Traversal.dashi-first-link-edge
  platoHyperformalCoordinate
  platoPhilosophyCoordinate
  Traversal.formulatedBy
  Traversal.canonicalDashiFirstLinkPolicy
  "structural cross-pollination routes back to the Plato philosophy formulation owner; Dewey/QID/source identity remain coordinates only"
  true

------------------------------------------------------------------------
-- Boundary / authority firewall.
------------------------------------------------------------------------

record PlatoSymposiumIndexingBoundary : Set where
  constructor plato-symposium-indexing-boundary
  field
    snowballSourceRoleRetentionRequired : Bool
    primarySecondaryRoleRetained : Bool
    deweyUsedForTraversal : Bool
    qidUsedForTraversal : Bool
    paretoUsedForConsumerRelativeWorkSelection : Bool

    qidCreatesSourceAuthority : Bool
    deweyCreatesSourceAuthority : Bool
    citationCountCreatesIndependence : Bool
    paretoRankCreatesConsumerAdequacy : Bool
    formalisationReplacesPrimaryHistoricalSource : Bool
    dashiBridgeReplacesJMDFormalisation : Bool
    indexCoordinateReplacesFormulationOwner : Bool

open PlatoSymposiumIndexingBoundary public

canonicalPlatoSymposiumIndexingBoundary : PlatoSymposiumIndexingBoundary
canonicalPlatoSymposiumIndexingBoundary =
  plato-symposium-indexing-boundary
    true true true true true
    false false false false false false false

qidStillNotProof : Traversal.QidIdentityCreatesProof → ⊥
qidStillNotProof = Traversal.qidIdentityIsNotProof

deweyStillNotSemanticEdge : Traversal.DeweyAdjacencyCreatesSemanticEdge → ⊥
deweyStillNotSemanticEdge = Traversal.deweyAdjacencyIsNotSemanticEdge

paretoStillNotProofAuthority :
  Pareto.paretoFrontierRefinementCreatesProofAuthority
    Pareto.canonicalRecursiveParetoFrontierBoundary ≡ false
paretoStillNotProofAuthority = refl

citationStillNotAuthority : Snowball.CitationCreatesDomainAuthority → ⊥
citationStillNotAuthority = Snowball.citationDoesNotCreateAuthority

indexingSummary : String
indexingSummary =
  "Plato/JMD/DASHI source roles snowball with provenance; Dewey and QID route traversal, citation count does not establish independence, and Pareto position selects residual-relevant work without creating consumer adequacy, proof, historical identity or source authority."
