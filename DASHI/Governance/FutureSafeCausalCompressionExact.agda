module DASHI.Governance.FutureSafeCausalCompressionExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Author: David Blackwell.
-- Title: "Equivalent Comparisons of Experiments".
-- Venue: The Annals of Mathematical Statistics 24(2), 265--272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- Blackwell supplies comparison-of-information / experiment vocabulary only.
-- The exact future-language and causal-compression constructions below are
-- DASHI constructions.
--
-- Existing repository producers reused directly:
--   * DASHI.Core.FutureObservationLanguageQuotientExact
--       kernel containment in future observational equivalence;
--   * PR #549 / AttackerObservationLanguageRefinementExact
--       observation-language refinement and separating observations;
--   * PR #556 / CausalResolutionExact
--       endpoint-preserving graph compression and reification collision loss.
--
-- The future-equivalence object is NOT redefined here.  This governance bridge
-- consumes the already-existing core theorem and adds the causal/query-relative
-- notion needed to distinguish safe abstraction from reification loss.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Governance.CausalResolutionExact as Resolution
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

------------------------------------------------------------------------
-- Future-safe causal edge compression.
------------------------------------------------------------------------

record FutureSafeEdgeCompression
  (Fine Coarse : Resolution.CausalGraph)
  (C : Resolution.GraphCompression Fine Coarse) : Set₁ where
  constructor futureSafeEdgeCompression
  field
    Action : Set
    Observation : Set
    system :
      Dependency.DependentActionSystem
        (Resolution.Edge Fine) Action
    project : Resolution.Edge Fine → Observation
    futureSafety :
      Future.FutureLanguageSafeProjection
        system
        project
        (Resolution.GraphCompression.edgeMap C)

open FutureSafeEdgeCompression public

compressedEdgesAreFutureEquivalent :
  ∀ {Fine Coarse : Resolution.CausalGraph}
    {C : Resolution.GraphCompression Fine Coarse}
    (safe : FutureSafeEdgeCompression Fine Coarse C)
    {left right : Resolution.Edge Fine} →
  Resolution.GraphCompression.edgeMap C left
    ≡ Resolution.GraphCompression.edgeMap C right →
  Future.FutureObservationEquivalent
    (system safe)
    (project safe)
    left right
compressedEdgesAreFutureEquivalent safe collision =
  Future.kernelContainedInFutureEquivalence
    (futureSafety safe)
    collision

------------------------------------------------------------------------
-- Query-relative causal resolution.
--
-- A coarse causal category is not condemned merely because it merges fine
-- edges.  Resolution is lost relative to a declared query language exactly
-- when a query can distinguish edges that the compression identifies.
------------------------------------------------------------------------

record EdgeQueryLanguage
  (G : Resolution.CausalGraph) : Set₁ where
  constructor edgeQueryLanguage
  field
    Query : Set
    Result : Set
    observeEdge : Query → Resolution.Edge G → Result

open EdgeQueryLanguage public

record QuerySafeCompression
  (Fine Coarse : Resolution.CausalGraph)
  (C : Resolution.GraphCompression Fine Coarse)
  (L : EdgeQueryLanguage Fine) : Set₁ where
  constructor querySafeCompression
  field
    compressedEdgesQueryEquivalent :
      ∀ {left right : Resolution.Edge Fine} →
      Resolution.GraphCompression.edgeMap C left
        ≡ Resolution.GraphCompression.edgeMap C right →
      (query : Query L) →
      observeEdge L query left ≡ observeEdge L query right

open QuerySafeCompression public

record ObservationRelevantReificationLoss
  (Fine Coarse : Resolution.CausalGraph)
  (C : Resolution.GraphCompression Fine Coarse)
  (L : EdgeQueryLanguage Fine) : Set₁ where
  constructor observationRelevantReificationLoss
  field
    baseLoss : Resolution.ReificationLoss Fine Coarse C
    separatingQuery : Query L
    querySeparatesCollapsedEdges :
      observeEdge L separatingQuery
        (Resolution.ReificationLoss.leftEdge baseLoss)
      ≡
      observeEdge L separatingQuery
        (Resolution.ReificationLoss.rightEdge baseLoss)
      → ⊥

open ObservationRelevantReificationLoss public

querySafeCompressionExcludesRelevantReificationLoss :
  ∀ {Fine Coarse : Resolution.CausalGraph}
    {C : Resolution.GraphCompression Fine Coarse}
    {L : EdgeQueryLanguage Fine} →
  QuerySafeCompression Fine Coarse C L →
  ObservationRelevantReificationLoss Fine Coarse C L →
  ⊥
querySafeCompressionExcludesRelevantReificationLoss safe loss =
  querySeparatesCollapsedEdges loss
    (compressedEdgesQueryEquivalent safe
      (Resolution.ReificationLoss.compressedTogether (baseLoss loss))
      (separatingQuery loss))

------------------------------------------------------------------------
-- Positive safe-compression witness: if a compression kernel is contained in
-- the equivalence induced by every declared query, then any collision is
-- observationally harmless for this query language.  This is relative safety,
-- not universal semantic identity.
------------------------------------------------------------------------

record QueryKernelEquivalence
  (G : Resolution.CausalGraph)
  (L : EdgeQueryLanguage G)
  (left right : Resolution.Edge G) : Set where
  constructor queryKernelEquivalence
  field
    allQueriesAgree :
      (query : Query L) →
      observeEdge L query left ≡ observeEdge L query right

querySafeCollisionProducesKernelEquivalence :
  ∀ {Fine Coarse : Resolution.CausalGraph}
    {C : Resolution.GraphCompression Fine Coarse}
    {L : EdgeQueryLanguage Fine}
    (safe : QuerySafeCompression Fine Coarse C L)
    {left right : Resolution.Edge Fine} →
  Resolution.GraphCompression.edgeMap C left
    ≡ Resolution.GraphCompression.edgeMap C right →
  QueryKernelEquivalence Fine L left right
querySafeCollisionProducesKernelEquivalence safe collision =
  queryKernelEquivalence
    (compressedEdgesQueryEquivalent safe collision)

------------------------------------------------------------------------
-- Governance boundary and provenance receipt.
------------------------------------------------------------------------

record FutureSafeCausalCompressionBoundary : Set where
  constructor futureSafeCausalCompressionBoundary
  field
    everyCompressionIsReificationLoss : Bool
    relevantDistinctionRequiresDeclaredQuery : Bool
    querySafeCollisionPreservesDeclaredObservations : Bool
    querySafetyImpliesUniversalOntologicalIdentity : Bool
    moreDetailIsAlwaysBetter : Bool
    futureSafetyIsRelativeToActionObservationLanguage : Bool
    futureEquivalenceCoreReusedRatherThanRedefined : Bool

canonicalFutureSafeCausalCompressionBoundary :
  FutureSafeCausalCompressionBoundary
canonicalFutureSafeCausalCompressionBoundary =
  futureSafeCausalCompressionBoundary
    false
    true
    true
    false
    false
    true
    true

record FutureSafeCausalCompressionReceipt : Set where
  constructor futureSafeCausalCompressionReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : FutureSafeCausalCompressionBoundary

canonicalFutureSafeCausalCompressionReceipt :
  FutureSafeCausalCompressionReceipt
canonicalFutureSafeCausalCompressionReceipt =
  futureSafeCausalCompressionReceipt
    (Sources.blackwellExperimentComparison ∷ [])
    canonicalFutureSafeCausalCompressionBoundary
