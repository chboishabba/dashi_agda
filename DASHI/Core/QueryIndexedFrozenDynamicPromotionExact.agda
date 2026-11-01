module DASHI.Core.QueryIndexedFrozenDynamicPromotionExact where

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen

------------------------------------------------------------------------
-- QUERY-INDEXED FUTURE-SAFE PROMOTION
--
-- The generic frozen/dynamic packet is not by itself a consumer-closure proof:
-- a strict refinement may separate one witnessed collision while still failing
-- to carry enough information for the whole declared query.  This owner adds
-- exactly that missing coordinate: query-indexed factorisation through the
-- joined observer.
--
-- Thus promotion requires all three independent payments:
--
--   1. provenance-aware strict static refinement + frozen selection receipt;
--   2. query adequacy of the refined observer;
--   3. dynamic trace congruence of the refined observer.
------------------------------------------------------------------------

record QueryIndexedFutureSafePromotion
    {State Action Surface Provenance QueryKey Answer : Set}
    (system : Dependency.DependentActionSystem State Action)
    (surface : State → Surface)
    (provenance : State → Provenance)
    (Rule : Set)
    (semantics : Query.QuerySemantics State QueryKey Answer)
    (query : QueryKey) : Set₁ where
  constructor query-indexed-future-safe-promotion
  field
    frozenDynamic :
      Frozen.FrozenProvenanceDynamicPromotion
        system surface provenance Rule
    queryAdequacy :
      Query.AdequateFor
        (Frozen.ProvenanceJoin surface provenance)
        semantics query

open QueryIndexedFutureSafePromotion public

queryStaticCandidate :
  ∀ {State Action Surface Provenance Rule QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey} →
  (promotion :
    QueryIndexedFutureSafePromotion
      system surface provenance Rule semantics query) →
  Frozen.FrozenStaticRefinementCandidate {Rule = Rule} surface provenance
queryStaticCandidate promotion =
  Frozen.staticCandidate (frozenDynamic promotion)

queryDynamicSafety :
  ∀ {State Action Surface Provenance Rule QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey} →
  QueryIndexedFutureSafePromotion
    system surface provenance Rule semantics query →
  Dynamic.DynamicConsumerSafety
    system (Frozen.ProvenanceJoin surface provenance)
queryDynamicSafety promotion =
  Frozen.dynamicSafety (frozenDynamic promotion)

queryFrozenSelection :
  ∀ {State Action Surface Provenance Rule QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey} →
  (promotion :
    QueryIndexedFutureSafePromotion
      system surface provenance Rule semantics query) →
  Frozen.FrozenSelectionReceipt Rule
queryFrozenSelection promotion =
  Frozen.promotionRetainsFrozenSelection (frozenDynamic promotion)

queryStaticStrictRefinement :
  ∀ {State Action Surface Provenance Rule QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey} →
  (promotion :
    QueryIndexedFutureSafePromotion
      system surface provenance Rule semantics query) →
  Observer.StrictRefinement
    surface (Frozen.ProvenanceJoin surface provenance)
queryStaticStrictRefinement promotion =
  Frozen.promotionRetainsStaticStrictRefinement (frozenDynamic promotion)

------------------------------------------------------------------------
-- A repaired/refined observer does not retroactively make the old coarse
-- observer adequate.  The coarse defect remains a valid obstruction on the old
-- surface even when a new promotion succeeds through a richer observer.
------------------------------------------------------------------------

coarseQueryDefectStillBlocksCoarseAdequacy :
  ∀ {State Action Surface Provenance Rule QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey} →
  Query.QueryAdequacyDefect surface semantics query →
  QueryIndexedFutureSafePromotion
    system surface provenance Rule semantics query →
  Query.AdequateFor surface semantics query →
  ⊥
coarseQueryDefectStillBlocksCoarseAdequacy defect promotion =
  Query.queryAdequacyDefectBlocksFactorisation defect

------------------------------------------------------------------------
-- Dynamic defects remain independently fatal after query closure.
------------------------------------------------------------------------

terminalisationDefectBlocksQueryPromotion :
  ∀ {State Action Surface Provenance Rule QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey} →
  Dynamic.TerminalisationDefect
    system (Frozen.ProvenanceJoin surface provenance) →
  QueryIndexedFutureSafePromotion
    system surface provenance Rule semantics query →
  ⊥
terminalisationDefectBlocksQueryPromotion defect promotion =
  Dynamic.terminalisationDefectContradictsSafety
    (queryDynamicSafety promotion)
    defect

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data QueryAdequacyAloneCreatesFutureSafetyPermission : Set where
data DynamicSafetyAloneCreatesQueryAdequacyPermission : Set where
data RefinedAdequacyRewritesCoarseHistoryPermission : Set where

queryAdequacyAloneDoesNotCreateFutureSafety :
  QueryAdequacyAloneCreatesFutureSafetyPermission → ⊥
queryAdequacyAloneDoesNotCreateFutureSafety ()

dynamicSafetyAloneDoesNotCreateQueryAdequacy :
  DynamicSafetyAloneCreatesQueryAdequacyPermission → ⊥
dynamicSafetyAloneDoesNotCreateQueryAdequacy ()

refinedAdequacyDoesNotRewriteCoarseHistory :
  RefinedAdequacyRewritesCoarseHistoryPermission → ⊥
refinedAdequacyDoesNotRewriteCoarseHistory ()
