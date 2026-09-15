module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceBoundedConsumerSafeFuturePromotionExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerSafeRefinementPromotionExact as StaticCore
import DASHI.Core.ConsumerSafeFuturePromotionExact as Composite
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConsumerSafePromotionExact as Static
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverParetoExact as Pareto
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceBoundedFutureDynamicsExact as Dynamics
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisExact as Third
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph

------------------------------------------------------------------------
-- SOURCE-BOUNDED ADK CONSUMER-SAFE FUTURE PROMOTION
--
-- This replaces the earlier zero-action interface fixture as the preferred AdK
-- roadmap witness.  The static side remains the same consumer-indexed
-- joinedTwo->threeAxis repair and Pareto selection.  The future side is now the
-- non-empty six-edge source-bounded graph action system.
--
-- The realisation relation is still an application-owned bridge: it states that
-- the selected `threeAxis` repository model is realised by the concrete
-- three-axis observation retained while the independent graph coordinate moves.
-- It does not identify the finite ThirdAxisWorld constructors with alpha..xi.
------------------------------------------------------------------------

data AdKSelectedModelRealisesSourceBoundedFuture :
  Pareto.ObserverModel →
  (Dynamics.AdKDynamicState →
    Dynamics.AdKFutureSurface × Third.NmpCoreAngleCoordinate) →
  Set where
  threeAxisRealisesSourceBoundedFuture :
    AdKSelectedModelRealisesSourceBoundedFuture
      Pareto.threeAxis
      Dynamics.adkFutureObservation

adkSourceBoundedConsumerSafeFuturePromotion :
  Composite.ConsumerSafeFuturePromotion
    Static.thirdAxisCostHyperfabric
    Pareto.joinedTwo
    Pareto.threeAxis
    Dynamics.adkSourceBoundedActionSystem
    Dynamics.adkFutureSurface
    Dynamics.adkFutureProvenance
    Dynamics.AdKGraphFreezeRule
    Dynamics.dynamicThirdAxisSemantics
    Third.askThirdCoordinate
    AdKSelectedModelRealisesSourceBoundedFuture
adkSourceBoundedConsumerSafeFuturePromotion =
  Composite.consumer-safe-future-promotion
    Static.adkThirdAxisConsumerSafePromotion
    Dynamics.adkGraphQueryIndexedFutureSafePromotion
    threeAxisRealisesSourceBoundedFuture

staticSafeSelectionRetained :
  StaticCore.ConsumerSafeSelectionReceipt
    Static.thirdAxisCostHyperfabric
    Pareto.threeAxis
staticSafeSelectionRetained =
  Composite.staticSafeSelection adkSourceBoundedConsumerSafeFuturePromotion

dynamicSafetyRetained :
  Dynamic.DynamicConsumerSafety
    Dynamics.adkSourceBoundedActionSystem
    Dynamics.adkFutureObservation
dynamicSafetyRetained =
  Composite.selectedObserverDynamicSafe
    adkSourceBoundedConsumerSafeFuturePromotion

queryAdequacyRetained :
  Query.AdequateFor
    Dynamics.adkFutureObservation
    Dynamics.dynamicThirdAxisSemantics
    Third.askThirdCoordinate
queryAdequacyRetained =
  Composite.selectedObserverQueryAdequate
    adkSourceBoundedConsumerSafeFuturePromotion

frozenSelectionRetained :
  Frozen.FrozenSelectionReceipt Dynamics.AdKGraphFreezeRule
frozenSelectionRetained =
  Composite.selectedObserverFrozen
    adkSourceBoundedConsumerSafeFuturePromotion

selectedRealisationRetained :
  AdKSelectedModelRealisesSourceBoundedFuture
    Pareto.threeAxis
    Dynamics.adkFutureObservation
selectedRealisationRetained =
  Composite.selectedModelRealisesFutureObserver
    adkSourceBoundedConsumerSafeFuturePromotion

------------------------------------------------------------------------
-- Attribution remains split by owner/source role.
------------------------------------------------------------------------

weightedGraphSourceDonor : Graph.WeightedGraphSourceCoordinate
weightedGraphSourceDonor = Graph.liLiuJi2015WeightedGraphSource

record AdKSourceBoundedConsumerSafeFutureBoundary : Set where
  constructor adk-source-bounded-consumer-safe-future-boundary
  field
    nontrivialGraphFuturePromotionComposed : Bool
    staticParetoSelectionRetained : Bool
    dynamicSafetyRetained : Bool
    queryAdequacyRetained : Bool
    frozenSelectionRetained : Bool
    selectedModelRealisationExplicit : Bool
    graphAndThirdAxisFixtureSilentlyIdentified : Bool
    compositeEqualsExperimentalKineticModel : Bool
    pathFluxPromotedToPerEdgeRate : Bool
    sourcePaperPaysGenericCompositeTheorem : Bool
    genericCompositeTransfersSourceAuthorship : Bool

canonicalAdKSourceBoundedConsumerSafeFutureBoundary :
  AdKSourceBoundedConsumerSafeFutureBoundary
canonicalAdKSourceBoundedConsumerSafeFutureBoundary =
  adk-source-bounded-consumer-safe-future-boundary
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
