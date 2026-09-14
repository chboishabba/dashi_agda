module DASHI.Core.QueryIndexedFrozenDynamicPromotionRegression where

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen
import DASHI.Core.QueryIndexedFrozenDynamicPromotionExact as Promotion

------------------------------------------------------------------------
-- RED/GREEN CONTRACT
------------------------------------------------------------------------

queryPromotionCarriesAdequacySurface :
  ∀ {State Action Surface Provenance Rule QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey} →
  Promotion.QueryIndexedFutureSafePromotion
    system surface provenance Rule semantics query →
  Query.AdequateFor
    (Observer.pairObserver surface provenance)
    semantics query
queryPromotionCarriesAdequacySurface = Promotion.queryAdequacy

queryPromotionCarriesDynamicSafetySurface :
  ∀ {State Action Surface Provenance Rule QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey} →
  Promotion.QueryIndexedFutureSafePromotion
    system surface provenance Rule semantics query →
  Dynamic.DynamicConsumerSafety system (Observer.pairObserver surface provenance)
queryPromotionCarriesDynamicSafetySurface =
  Promotion.queryDynamicSafety

coarseQueryDefectRemainsBlockedSurface :
  ∀ {State Action Surface Provenance Rule QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey} →
  Query.QueryAdequacyDefect surface semantics query →
  Promotion.QueryIndexedFutureSafePromotion
    system surface provenance Rule semantics query →
  Query.AdequateFor surface semantics query →
  ⊥
coarseQueryDefectRemainsBlockedSurface =
  Promotion.coarseQueryDefectStillBlocksCoarseAdequacy
