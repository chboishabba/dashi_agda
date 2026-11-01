module DASHI.Core.FrozenProvenanceDynamicRefinementRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen

------------------------------------------------------------------------
-- RED/GREEN CONTRACT
------------------------------------------------------------------------

provenanceJoinStrictRefinementSurface :
  ∀ {State Surface Provenance : Set}
    (surface : State → Surface)
    (provenance : State → Provenance)
    (left right : State) →
  surface left ≡ surface right →
  (provenance left ≡ provenance right → ⊥) →
  Observer.StrictRefinement surface (Observer.pairObserver surface provenance)
provenanceJoinStrictRefinementSurface = Frozen.provenanceJoinStrictRefinement

futureSafePromotionCarriesDynamicSafetySurface :
  ∀ {State Action Surface Provenance Rule : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance} →
  Frozen.FrozenProvenanceDynamicPromotion system surface provenance Rule →
  Dynamic.DynamicConsumerSafety system (Observer.pairObserver surface provenance)
futureSafePromotionCarriesDynamicSafetySurface =
  Frozen.dynamicSafety

terminalisationDefectBlocksFrozenPromotionSurface :
  ∀ {State Action Surface Provenance Rule : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance} →
  Dynamic.TerminalisationDefect system (Observer.pairObserver surface provenance) →
  Frozen.FrozenProvenanceDynamicPromotion system surface provenance Rule →
  ⊥
terminalisationDefectBlocksFrozenPromotionSurface =
  Frozen.terminalisationDefectBlocksFrozenPromotion
