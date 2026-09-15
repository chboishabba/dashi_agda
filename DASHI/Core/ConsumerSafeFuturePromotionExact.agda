module DASHI.Core.ConsumerSafeFuturePromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerSafeRefinementPromotionExact as Static
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen
import DASHI.Core.QueryIndexedFrozenDynamicPromotionExact as Future
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- CONSUMER-SAFE FUTURE PROMOTION
--
-- This is the thin weld between two already-existing, independently paid DASHI
-- theorem families:
--
--   static consumer-safe selection
--     counterexample -> local repair -> eligibility -> minimal/Pareto selection
--
--   query-indexed future-safe observation
--     strict provenance-aware refinement + frozen selection
--       + query adequacy + dynamic trace congruence.
--
-- Neither side is allowed to manufacture the other.  An application must also
-- pay a realisation relation connecting the selected MDL model to the concrete
-- future-safe observer.  Mere coexistence of two receipts is insufficient.
------------------------------------------------------------------------

record ConsumerSafeFuturePromotion
    {problem : MDL.ConsumerMDLProblem}
    (costs : MDL.CostHyperfabric problem)
    (coarse fine : MDL.Model problem)
    {State Action Surface Provenance QueryKey Answer : Set}
    (system : Dependency.DependentActionSystem State Action)
    (surface : State → Surface)
    (provenance : State → Provenance)
    (Rule : Set)
    (semantics : Query.QuerySemantics State QueryKey Answer)
    (query : QueryKey)
    (Realises :
      MDL.Model problem →
      (State → Surface × Provenance) →
      Set) : Set₁ where
  constructor consumer-safe-future-promotion
  field
    staticPromotion :
      Static.ConsumerSafeRefinementPromotion costs coarse fine

    futurePromotion :
      Future.QueryIndexedFutureSafePromotion
        system surface provenance Rule semantics query

    selectedRealisation :
      Realises fine (Frozen.ProvenanceJoin surface provenance)

open ConsumerSafeFuturePromotion public

------------------------------------------------------------------------
-- Static consumer-safe selection is retained exactly.
------------------------------------------------------------------------

staticSafeSelection :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem}
    {State Action Surface Provenance QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {Rule : Set}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey}
    {Realises : MDL.Model problem → (State → Surface × Provenance) → Set} →
  ConsumerSafeFuturePromotion
    costs coarse fine system surface provenance Rule semantics query Realises →
  Static.ConsumerSafeSelectionReceipt costs fine
staticSafeSelection promotion =
  Static.promotionProducesSafeSelection (staticPromotion promotion)

selectedModelEligible :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem}
    {State Action Surface Provenance QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {Rule : Set}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey}
    {Realises : MDL.Model problem → (State → Surface × Provenance) → Set} →
  ConsumerSafeFuturePromotion
    costs coarse fine system surface provenance Rule semantics query Realises →
  MDL.Eligible problem fine
selectedModelEligible promotion =
  Static.eligible (staticSafeSelection promotion)

------------------------------------------------------------------------
-- Future-safe observation payments are retained independently.
------------------------------------------------------------------------

selectedObserverQueryAdequate :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem}
    {State Action Surface Provenance QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {Rule : Set}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey}
    {Realises : MDL.Model problem → (State → Surface × Provenance) → Set} →
  ConsumerSafeFuturePromotion
    costs coarse fine system surface provenance Rule semantics query Realises →
  Query.AdequateFor
    (Frozen.ProvenanceJoin surface provenance)
    semantics query
selectedObserverQueryAdequate promotion =
  Future.queryAdequacy (futurePromotion promotion)

selectedObserverDynamicSafe :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem}
    {State Action Surface Provenance QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {Rule : Set}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey}
    {Realises : MDL.Model problem → (State → Surface × Provenance) → Set} →
  ConsumerSafeFuturePromotion
    costs coarse fine system surface provenance Rule semantics query Realises →
  Dynamic.DynamicConsumerSafety
    system (Frozen.ProvenanceJoin surface provenance)
selectedObserverDynamicSafe promotion =
  Future.queryDynamicSafety (futurePromotion promotion)

selectedObserverFrozen :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem}
    {State Action Surface Provenance QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {Rule : Set}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey}
    {Realises : MDL.Model problem → (State → Surface × Provenance) → Set} →
  ConsumerSafeFuturePromotion
    costs coarse fine system surface provenance Rule semantics query Realises →
  Frozen.FrozenSelectionReceipt Rule
selectedObserverFrozen promotion =
  Future.queryFrozenSelection (futurePromotion promotion)

selectedObserverStrictlyRefinesSurface :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem}
    {State Action Surface Provenance QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {Rule : Set}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey}
    {Realises : MDL.Model problem → (State → Surface × Provenance) → Set} →
  ConsumerSafeFuturePromotion
    costs coarse fine system surface provenance Rule semantics query Realises →
  Observer.StrictRefinement
    surface (Frozen.ProvenanceJoin surface provenance)
selectedObserverStrictlyRefinesSurface promotion =
  Future.queryStaticStrictRefinement (futurePromotion promotion)

------------------------------------------------------------------------
-- The application bridge is retained as its own payment.
------------------------------------------------------------------------

selectedModelRealisesFutureObserver :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem}
    {State Action Surface Provenance QueryKey Answer : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance}
    {Rule : Set}
    {semantics : Query.QuerySemantics State QueryKey Answer}
    {query : QueryKey}
    {Realises : MDL.Model problem → (State → Surface × Provenance) → Set} →
  (promotion :
    ConsumerSafeFuturePromotion
      costs coarse fine system surface provenance Rule semantics query Realises) →
  Realises fine (Frozen.ProvenanceJoin surface provenance)
selectedModelRealisesFutureObserver = selectedRealisation

------------------------------------------------------------------------
-- Boundaries: static safety, future safety, and realisation do not collapse.
------------------------------------------------------------------------

record ConsumerSafeFuturePromotionBoundary : Set where
  constructor consumer-safe-future-promotion-boundary
  field
    staticPromotionRetained : Bool
    futureSafePromotionRetained : Bool
    selectedModelRealisationRequired : Bool
    queryAdequacyRetained : Bool
    dynamicSafetyRetained : Bool
    frozenSelectionRetained : Bool
    staticConsumerSafetyAloneImpliesFutureSafety : Bool
    futureSafetyAloneImpliesParetoSelection : Bool
    realisationWitnessCreatesEmpiricalTruth : Bool
    futureSafeMeansWorldComplete : Bool
    crossDomainReuseTransfersAuthorship : Bool

canonicalConsumerSafeFuturePromotionBoundary :
  ConsumerSafeFuturePromotionBoundary
canonicalConsumerSafeFuturePromotionBoundary =
  consumer-safe-future-promotion-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Attribution firewall.
------------------------------------------------------------------------

record ConsumerSafeFutureAttributionFirewall : Set where
  constructor consumer-safe-future-attribution-firewall
  field
    staticOwner : String
    futureOwner : String
    applicationOwner : String
    transferRule : String

canonicalConsumerSafeFutureAttributionFirewall :
  ConsumerSafeFutureAttributionFirewall
canonicalConsumerSafeFutureAttributionFirewall =
  consumer-safe-future-attribution-firewall
    "DASHI ConsumerSafeRefinementPromotion: consumer counterexample, local repair, eligibility, minimal/Pareto selection"
    "DASHI QueryIndexedFrozenDynamicPromotion: frozen provenance-aware refinement, query adequacy, dynamic trace safety"
    "application pays the model-to-observer realisation witness and all domain/source premises"
    "composition transfers structure only; it does not transfer source authorship, empirical truth, mechanism, authority, or world-completeness"
