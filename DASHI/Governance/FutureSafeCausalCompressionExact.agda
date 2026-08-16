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
-- Internal producer pollen:
--   * PR #548 / DASHI.Core.FutureObservationLanguageQuotientExact
--       kernel containment in future observational equivalence;
--   * PR #549 / AttackerObservationLanguageRefinementExact
--       observation-language refinement and separating observations;
--   * PR #556 / CausalResolutionExact
--       endpoint-preserving graph compression and reification collision loss.
--
-- This module is deliberately self-contained over the #556 branch.  It ports
-- only the theorem shape needed by governance consumers; it does not duplicate
-- the full #548 future-quotient compiler or the crypto-specific #549 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Governance.CausalResolutionExact as Resolution

------------------------------------------------------------------------
-- Future observational equivalence.
------------------------------------------------------------------------

record DynamicObservationSystem : Set₁ where
  constructor dynamicObservationSystem
  field
    State : Set
    Action : Set
    Observation : Set
    step : Action → State → State
    observe : State → Observation

open DynamicObservationSystem public

run :
  (S : DynamicObservationSystem) →
  List (Action S) → State S → State S
run S [] state = state
run S (action ∷ actions) state =
  run S actions (step S action state)

record FutureEquivalent
  (S : DynamicObservationSystem)
  (left right : State S) : Set where
  constructor futureEquivalent
  field
    sameFutureObservation :
      (actions : List (Action S)) →
      observe S (run S actions left)
      ≡ observe S (run S actions right)

open FutureEquivalent public

futureEquivalentRefl :
  (S : DynamicObservationSystem) →
  (state : State S) →
  FutureEquivalent S state state
futureEquivalentRefl S state =
  futureEquivalent (λ actions → refl)

record FutureSafeCoarsening
  (S : DynamicObservationSystem)
  (Coarse : Set) : Set₁ where
  constructor futureSafeCoarsening
  field
    coarsen : State S → Coarse
    kernelContainedInFutureEquivalence :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      FutureEquivalent S left right

open FutureSafeCoarsening public

safeCollisionIsFutureInvisible :
  ∀ {S : DynamicObservationSystem}
    {Coarse : Set}
    (safe : FutureSafeCoarsening S Coarse)
    {left right : State S} →
  coarsen safe left ≡ coarsen safe right →
  FutureEquivalent S left right
safeCollisionIsFutureInvisible safe =
  kernelContainedInFutureEquivalence safe

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
-- Governance boundary.
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
